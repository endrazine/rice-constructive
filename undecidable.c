/*
 * undecidable.c
 *
 * A faithful executable witness of the two-witness family S_D from
 *
 *     "A Constructive Proof of Rice's Theorem and the Halting Problem
 *      via Hilbert's Tenth Problem"
 *
 * The program takes ONE argument: a Diophantine polynomial D with integer
 * coefficients in the variables x1, x2, ..., xk, whose variables range over
 * the natural numbers. (This is the paper's Poly: Z coefficients, evaluated
 * at N-tuples.) It searches N^k for a tuple with D = 0, and:
 *
 *     - HALTS, printing the witness, if and only if D has a solution;
 *     - runs forever if D has no solution.
 *
 * This is the executable image of  S_D_solvable_equiv / S_D_unsolvable_equiv:
 *
 *         U(D) halts   <=>   D is solvable over N.
 *
 * The undecidability is NOT a property of any single run. For any fixed D,
 * "does U(D) halt?" is a single definite bit. What is undecidable is the
 * map  D |-> halts(U, D)  over ALL inputs D: an algorithm deciding it would
 * decide N-Diophantine solvability, contradicting MRDP (H10C_SAT_undec).
 * That is Theorem 5.1 (Rice) instantiated at the Terminates property.
 *
 * MODEL FAITHFULNESS. The search over N^k is unbounded, matching the
 * idealized model the Rocq development formalizes. On a real machine an
 * unsolvable input runs until memory is exhausted and the process is
 * killed; that physical death is the observable shadow of divergence, not
 * a decision. The program NEVER halts without exhibiting a genuine
 * solution, and NEVER reports "no solution" -- it cannot, and saying so
 * would be to claim a decider that MRDP forbids.
 *
 * All arithmetic is exact (GMP mpz). A false zero from overflow would break
 * the equivalence in the fatal direction, so nothing that feeds a "= 0"
 * test is ever computed in fixed-width arithmetic. Any allocation failure
 * aborts loudly rather than continuing in a corrupted state.
 *
 * Build (hardened, portable):
 *   cc -std=c17 -O2 -fPIE -pie -fstack-protector-all -D_FORTIFY_SOURCE=2 \
 *      -Wl,-z,relro -Wl,-z,now -o undecidable undecidable.c -lgmp
 * (A Makefile is provided that adds arch-specific mitigations when the
 *  toolchain supports them.) The hardening is good hygiene, not a
 *  response to a threat model: this program parses one polynomial from
 *  argv on the user's own command line -- no network, no file input, no
 *  privilege, no adversary. The load-bearing safety property is the
 *  exact-arithmetic, checked-allocation "never a false halt" discipline,
 *  which holds regardless of compiler flags.
 * Use:    ./undecidable "x1^2 - x2^2 - x3^2 - 1"     (halts at (1,0,0))
 *         ./undecidable "x1^2 + 1"                    (no solution: x1^2+1>=1, runs on)
 *
 * A note on "trusted core" below: it means the trusted computing base of
 * THIS executable. The Rocq development is what is formally verified; this
 * handwritten C is an unverified but faithful transcription of it, included
 * so the construction can be run and inspected.
 *
 * Author: Jonathan Brossard <endrazine@securityfocus.com>
 * License: Creative Commons Attribution (CC BY 4.0), as the paper.
 */

#include <gmp.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ================================================================== */
/*  fail  -- loud abort; GMP allocation failures route here.          */
/*  Trusted core. The one forbidden behaviour is quiet corruption      */
/*  by a "solution found": every failure path ends the process.       */
/* ================================================================== */

static void die(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    fputs("undecidable: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    exit(1);
}

static void *xalloc(size_t n)
{
    void *p = malloc(n);
    if (!p) die("out of memory (requested %zu bytes)", n);
    return p;
}

/* Checked array realloc: guards the count*size multiply against size_t
   overflow, then reallocs and checks the result (saving nothing to the
   caller's pointer until success, so a failed grow never nulls it).
   Aborts on either failure -- never returns NULL. */
static void *xreallocarray(void *p, size_t count, size_t size)
{
    if (size != 0 && count > (size_t)-1 / size)
        die("allocation size overflow (%zu * %zu)", count, size);
    void *q = realloc(p, count * size);
    if (!q) die("out of memory (realloc %zu bytes)", count * size);
    return q;
}

/* GMP calls these for every mpz limb allocation. On failure we abort;
   we never hand GMP a NULL and let it continue. */
static void *gmp_alloc(size_t n)                 { return xalloc(n); }
static void *gmp_realloc(void *p, size_t o, size_t n)
{
    (void)o;
    void *q = realloc(p, n);
    if (!q) die("out of memory (realloc to %zu bytes)", n);
    return q;
}
static void  gmp_free(void *p, size_t n)         { (void)n; free(p); }

/* ================================================================== */
/*  poly  -- the data. Mirrors the Rocq  Poly / Monomial types:       */
/*      Monomial := (Z coefficient, exponent vector over N)           */
/*      Poly     := list of monomials, all of a common arity k.       */
/*  Trusted core (this executable's TCB; see the header note).         */
/* ================================================================== */

typedef struct {
    mpz_t          coeff;   /* signed integer coefficient (Z)          */
    unsigned long *exp;     /* exponent vector, length = poly arity (N)*/
} monomial_t;

typedef struct {
    size_t      arity;      /* k: number of variables x1..xk           */
    size_t      nterms;     /* number of monomials                     */
    monomial_t *terms;      /* the monomials                           */
} poly_t;

/* eval_poly: exact evaluation of P at the tuple `vars` (length arity).
   Image of Rocq eval_poly / eval_monomial. Result in `out`. */
static void poly_eval(const poly_t *P, mpz_t *vars, mpz_t out)
{
    mpz_t term, p;
    mpz_init(term);
    mpz_init(p);
    mpz_set_ui(out, 0);

    for (size_t j = 0; j < P->nterms; j++) {
        mpz_set(term, P->terms[j].coeff);
        for (size_t i = 0; i < P->arity; i++) {
            unsigned long e = P->terms[j].exp[i];
            if (e != 0) {
                mpz_pow_ui(p, vars[i], e);   /* vars[i]^e, exact        */
                mpz_mul(term, term, p);
            }
        }
        mpz_add(out, out, term);
    }
    mpz_clear(term);
    mpz_clear(p);
}

/* ================================================================== */
/*  cantor  -- the enumeration of N^k. Faithful transcription of the  */
/*  Rocq decode_k built on Cantor unpairing:                          */
/*                                                                    */
/*      w(n)          = floor((sqrt(8n+1) - 1) / 2)                    */
/*      unpair_snd(n) = n - w(w+1)/2                                   */
/*      unpair_fst(n) = w - unpair_snd(n)                             */
/*      decode_k 1 n        = [n]                                     */
/*      decode_k (a+1>=2) n = decode_k a (fst n) ++ [snd n]           */
/*                                                                    */
/*  so the LAST coordinate is snd(n) and the rest come from fst(n).    */
/*  Every tuple of N^k is reached at some finite index n (fairness),   */
/*  which is what makes "solvable => halts" hold.                      */
/*  Trusted core (this executable's TCB; see the header note).         */
/* ================================================================== */

/* one Cantor unpairing step: given n, produce (fst, snd). */
static void cantor_unpair(const mpz_t n, mpz_t fst, mpz_t snd)
{
    mpz_t w, t, r;
    mpz_init(w);
    mpz_init(t);
    mpz_init(r);

    /* w = floor((sqrt(8n+1) - 1)/2) */
    mpz_mul_ui(t, n, 8);
    mpz_add_ui(t, t, 1);
    mpz_sqrt(w, t);              /* floor(sqrt(8n+1)) */
    mpz_sub_ui(w, w, 1);
    mpz_fdiv_q_ui(w, w, 2);

    /* t = w*(w+1)/2 */
    mpz_add_ui(r, w, 1);
    mpz_mul(t, w, r);
    mpz_fdiv_q_ui(t, t, 2);

    /* snd = n - t ; fst = w - snd */
    mpz_sub(snd, n, t);
    mpz_sub(fst, w, snd);

    mpz_clear(w);
    mpz_clear(t);
    mpz_clear(r);
}

/* decode index n into a k-tuple, writing vars[0..k-1] (x1..xk). */
static void decode_k(size_t arity, const mpz_t n, mpz_t *vars)
{
    if (arity == 0) return;             /* constant: empty tuple       */

    mpz_t cur, fst, snd;
    mpz_init_set(cur, n);
    mpz_init(fst);
    mpz_init(snd);

    /* peel the last coordinate repeatedly, down to the first */
    for (size_t i = arity - 1; i >= 1; i--) {
        cantor_unpair(cur, fst, snd);
        mpz_set(vars[i], snd);          /* last coord = snd(cur)       */
        mpz_set(cur, fst);              /* recurse on fst              */
    }
    mpz_set(vars[0], cur);              /* base: decode_k 1 n = [n]    */

    mpz_clear(cur);
    mpz_clear(fst);
    mpz_clear(snd);
}

/* check_solution: does P vanish at the tuple encoded by index n?
   Image of Rocq check_solution. */
static int check_solution(const poly_t *P, const mpz_t n, mpz_t *vars, mpz_t val)
{
    decode_k(P->arity, n, vars);
    poly_eval(P, vars, val);
    return mpz_sgn(val) == 0;
}

/* ================================================================== */
/*  search  -- the dovetail. Image of Rocq find_sol with fuel taken   */
/*  to infinity: n = 0, 1, 2, ... over an UNBOUNDED mpz counter (a     */
/*  fixed-width counter would silently make the search finite and      */
/*  break solvable => halts). On the first hit the witness is          */
/*  re-verified before anything is printed; there is exactly one       */
/*  success path in the whole program, and it holds a real solution.   */
/*  Trusted core (this executable's TCB; see the header note).         */
/* ================================================================== */

static void run_search(const poly_t *P)
{
    mpz_t n, val, recheck;
    mpz_t *vars = xalloc((P->arity ? P->arity : 1) * sizeof *vars);
    for (size_t i = 0; i < P->arity; i++) mpz_init(vars[i]);
    mpz_init(n);
    mpz_init(val);
    mpz_init(recheck);

    for (;;) {                          /* unbounded: no exit on "no solution" */
        if (check_solution(P, n, vars, val)) {
            /* re-verify the witness independently before claiming it. */
            poly_eval(P, vars, recheck);
            if (mpz_sgn(recheck) != 0)
                die("internal error: unverified witness (this is a bug)");

            printf("SOLUTION FOUND. D vanishes at:\n");
            for (size_t i = 0; i < P->arity; i++) {
                gmp_printf("    x%zu = %Zd\n", i + 1, vars[i]);
            }
            if (P->arity == 0) printf("    (no variables; constant is zero)\n");
            fflush(stdout);
            /* deliberate: the ONLY halting path, and it exhibits a witness. */
            for (size_t i = 0; i < P->arity; i++) mpz_clear(vars[i]);
            free(vars);
            mpz_clear(n); mpz_clear(val); mpz_clear(recheck);
            exit(0);
        }
        mpz_add_ui(n, n, 1);            /* next index; never wraps (mpz) */
    }
    /* unreachable */
}

/* ================================================================== */
/*  parse  -- UNTRUSTED convenience front-end.                        */
/*                                                                    */
/*  Turns "x1^3 + x2^3 + x3^3 - 33" into the poly_t above. The parser  */
/*  is NOT part of the mathematical reduction: the reduction begins    */
/*  from the poly_t consumed by the search core. The parser only       */
/*  translates text into that representation and echoes the result for */
/*  inspection, so nothing in the undecidability argument depends on    */
/*  it. (It is ordinary C and not memory-safety-proved; the echo is    */
/*  what lets a user confirm the polynomial actually built.)           */
/*                                                                    */
/*  Grammar (flat, no parentheses, no recursion):                     */
/*      poly := [sign] term ( sign term )*                            */
/*      term := factor ( '*' factor )*                                */
/*      factor := integer | var [ '^' integer ]                       */
/*      var  := 'x' digit+     (index >= 1)                           */
/*                                                                    */
/*  Whitelist-first: any byte outside [0-9 x + - ^ * whitespace] is    */
/*  rejected at its offset. Malformed tokens are rejected with the     */
/*  offset. No error recovery: produce the exact polynomial, or refuse.*/
/* ================================================================== */

/* A parsed term: signed coefficient plus an exponent map var->exp,
   stored sparsely as we accumulate (var index i in 1..k). */
typedef struct {
    mpz_t          coeff;
    unsigned long *exp;     /* exponent vector, grown on demand        */
    size_t         len;     /* current length of exp                   */
} term_acc_t;

/* Parser state over the input string. */
typedef struct {
    const char *s;          /* whole string (for offset reporting)     */
    const char *p;          /* cursor                                  */
    size_t      arity;      /* running max variable index              */
    /* collected terms */
    term_acc_t *terms;
    size_t      nterms;
    size_t      cap;
} parser_t;

static size_t off(parser_t *P) { return (size_t)(P->p - P->s); }

static void perr(parser_t *P, const char *msg)
{
    die("parse error at offset %zu (near \"%.12s\"): %s", off(P), P->p, msg);
}

static void skip_ws(parser_t *P)
{
    while (*P->p == ' ' || *P->p == '\t' || *P->p == '\n' || *P->p == '\r')
        P->p++;
}

/* read a run of digits into an mpz; error if none. */
static void read_uint(parser_t *P, mpz_t out)
{
    const char *start = P->p;
    while (*P->p >= '0' && *P->p <= '9') P->p++;
    if (P->p == start) perr(P, "expected a non-negative integer");
    char *buf = xalloc((size_t)(P->p - start) + 1);
    memcpy(buf, start, (size_t)(P->p - start));
    buf[P->p - start] = '\0';
    if (mpz_set_str(out, buf, 10) != 0) { free(buf); perr(P, "malformed integer"); }
    free(buf);
}

/* read a run of digits into an unsigned long (for exponents/indices);
   reject values that do not fit -- exponents beyond ulong are refused
   loudly rather than silently truncated. */
static unsigned long read_ulong(parser_t *P, const char *what)
{
    mpz_t z;
    mpz_init(z);
    read_uint(P, z);
    if (!mpz_fits_ulong_p(z)) { mpz_clear(z); perr(P, what); }
    unsigned long v = mpz_get_ui(z);
    mpz_clear(z);
    return v;
}

/* grow a term's exponent vector to at least `need` slots (zero-filled). */
static void ensure_len(term_acc_t *t, size_t need)
{
    if (need <= t->len) return;
    t->exp = xreallocarray(t->exp, need, sizeof *t->exp);
    for (size_t i = t->len; i < need; i++) t->exp[i] = 0;
    t->len = need;
}

/* Parse one term into `t` (coeff preset to +1 or -1 by caller).
   Multiplies integer factors into t->coeff and accumulates exponents. */
static void parse_term(parser_t *P, term_acc_t *t)
{
    int saw_factor = 0;
    for (;;) {
        skip_ws(P);
        char c = *P->p;

        if (c >= '0' && c <= '9') {              /* integer factor */
            mpz_t k;
            mpz_init(k);
            read_uint(P, k);
            mpz_mul(t->coeff, t->coeff, k);
            mpz_clear(k);
            saw_factor = 1;
        } else if (c == 'x') {                   /* variable factor */
            P->p++;                              /* consume 'x' */
            unsigned long idx = read_ulong(P, "variable index too large");
            if (idx == 0) perr(P, "variables are numbered from x1");
            /* grow this term's vector, and the global arity, to idx */
            ensure_len(t, idx);
            if (idx > P->arity) P->arity = idx;
            unsigned long e = 1;
            skip_ws(P);
            if (*P->p == '^') {
                P->p++;
                skip_ws(P);
                e = read_ulong(P, "exponent too large");
            }
            if (ULONG_MAX - t->exp[idx - 1] < e)
                perr(P, "accumulated exponent too large");
            t->exp[idx - 1] += e;                /* fold x1*x1 -> x1^2 */
            saw_factor = 1;
        } else {
            perr(P, "expected an integer or a variable xN");
        }

        skip_ws(P);
        if (*P->p == '*') { P->p++; continue; }  /* another factor */
        break;
    }
    if (!saw_factor) perr(P, "empty term");
}

/* whitelist scan: reject any byte outside the legal alphabet up front. */
static void whitelist_check(parser_t *P)
{
    for (const char *q = P->s; *q; q++) {
        char c = *q;
        int ok = (c >= '0' && c <= '9') || c == 'x' ||
                 c == '+' || c == '-' || c == '^' || c == '*' ||
                 c == ' ' || c == '\t' || c == '\n' || c == '\r';
        if (!ok) {
            P->p = q;
            perr(P, "illegal character");
        }
    }
}

/* Parse the whole polynomial string into a poly_t. */
static void parse_poly(const char *input, poly_t *out)
{
    parser_t P;
    P.s = input; P.p = input; P.arity = 0;
    P.terms = NULL; P.nterms = 0; P.cap = 0;

    whitelist_check(&P);
    P.p = input;

    skip_ws(&P);
    if (*P.p == '\0') perr(&P, "empty polynomial");

    int first = 1;
    for (;;) {
        skip_ws(&P);
        int sign = 1;

        if (first) {
            if (*P.p == '-') { sign = -1; P.p++; }
            else if (*P.p == '+') { P.p++; }
            first = 0;
        } else {
            if (*P.p == '\0') break;             /* clean end */
            if (*P.p == '+') { sign = 1; P.p++; }
            else if (*P.p == '-') { sign = -1; P.p++; }
            else perr(&P, "expected '+' or '-' between terms");
        }

        /* fresh accumulator */
        if (P.nterms == P.cap) {
            P.cap = P.cap ? P.cap * 2 : 8;
            P.terms = xreallocarray(P.terms, P.cap, sizeof *P.terms);
        }
        term_acc_t *t = &P.terms[P.nterms];
        mpz_init_set_si(t->coeff, sign);
        t->exp = NULL;
        t->len = 0;             /* grown on demand as variables appear */
        parse_term(&P, t);
        P.nterms++;

        skip_ws(&P);
        if (*P.p == '\0') break;
    }

    /* normalise: every term's exponent vector padded to final arity. */
    out->arity  = P.arity;
    out->nterms = P.nterms;
    out->terms  = xalloc(P.nterms * sizeof *out->terms);
    for (size_t j = 0; j < P.nterms; j++) {
        mpz_init_set(out->terms[j].coeff, P.terms[j].coeff);
        mpz_clear(P.terms[j].coeff);
        out->terms[j].exp = xalloc((P.arity ? P.arity : 1) * sizeof(unsigned long));
        for (size_t i = 0; i < P.arity; i++) {
            /* this term's vector was grown only to its own len */
            out->terms[j].exp[i] = (i < P.terms[j].len) ? P.terms[j].exp[i] : 0;
        }
        free(P.terms[j].exp);
    }
    free(P.terms);
}

/* Echo the polynomial we actually built, so the user confirms intent. */
static void echo_poly(const poly_t *P)
{
    printf("Understood polynomial over N (arity %zu):\n  ", P->arity);
    for (size_t j = 0; j < P->nterms; j++) {
        if (j) printf(" + ");
        gmp_printf("(%Zd)", P->terms[j].coeff);
        for (size_t i = 0; i < P->arity; i++) {
            if (P->terms[j].exp[i] == 1)      printf("*x%zu", i + 1);
            else if (P->terms[j].exp[i] > 1)  printf("*x%zu^%lu", i + 1, P->terms[j].exp[i]);
        }
    }
    printf(" = 0\n");
    printf("Searching N^%zu for a solution (halts iff one exists)...\n", P->arity);
    fflush(stdout);
}

/* ================================================================== */
/*  main  -- wire it together. Install the fail-loud GMP allocator     */
/*  first, then: parse -> echo -> search.                             */
/* ================================================================== */

int main(int argc, char **argv)
{
    mp_set_memory_functions(gmp_alloc, gmp_realloc, gmp_free);

    if (argc != 2) {
        fprintf(stderr,
            "usage: %s \"<polynomial in x1..xk>\"\n"
            "  e.g. %s \"x1^2 - x2^2 - x3^2 - 1\"   (halts at (1,0,0))\n"
            "       %s \"x1^2 + 1\"                   (no solution: runs on)\n",
            argv[0], argv[0], argv[0]);
        return 2;
    }

    poly_t D;
    parse_poly(argv[1], &D);
    echo_poly(&D);
    run_search(&D);        /* returns only via exit(0) on a witness */
    return 0;              /* unreachable */
}
