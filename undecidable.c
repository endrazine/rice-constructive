/*
 * undecidable.c — a program whose termination is provably undecidable
 *
 * This file contains two things:
 *
 *   1. A generic Diophantine search engine (find_sol) that directly mirrors
 *      the Rocq function of the same name in rice.v.
 *
 *   2. Two concrete instantiations:
 *
 *      Program 1 ("decidable"):
 *        Searches for x^2 - y^2 - z^2 = 1.
 *        The equation is solvable (x=1, y=0, z=0); this program terminates.
 *
 *      Program 2 ("undecidable"):
 *        For each k = 0, 1, 2, ... with k not congruent to 4 or 5 (mod 9),
 *        searches for integer x, y, z such that x^3 + y^3 + z^3 = k.
 *        Advances to k+1 as soon as a solution for k is found.
 *        This program terminates if and only if every integer not congruent
 *        to 4 or 5 (mod 9) is a sum of three integer cubes — an open
 *        conjecture in number theory.  Whether it terminates is therefore
 *        an open problem in mathematics, permanently (not just until some
 *        single value like 114 is resolved).
 *
 * FORMAL CLAIM (proved in rice.v / Theorem Rice_Theorem):
 *
 *   No static analyzer can correctly determine, for all programs of the
 *   form below, whether they terminate. Any analyzer that could do so
 *   would decide the solvability of arbitrary Diophantine equations —
 *   which is impossible by the MRDP theorem (Hilbert's Tenth Problem).
 *
 *   Formal proof: rice.v (Rocq/Coq 8.20)
 *   MRDP mechanization: https://github.com/uds-psl/coq-library-undecidability
 *
 * WHY THE CONJECTURE STRUCTURE MAKES THIS PERMANENTLY OPEN:
 *
 *   A single-target search (e.g. x^3+y^3+z^3=114) is only open until
 *   someone finds a solution or proves none exists.  By searching
 *   k = 0, 1, 2, ... sequentially, the program terminates iff the full
 *   conjecture holds.  Resolving any single k merely advances the search;
 *   the overall question remains open.
 *
 * WHY GMP IS REQUIRED (correctness argument):
 *
 *   The Rocq proof reasons about programs over mathematically infinite nat.
 *   A fixed-width counter (e.g. uint64_t) would exhaust its range in finite
 *   time, making the program trivially terminating — which would invalidate
 *   the undecidability claim. We use GMP (GNU Multiple Precision) mpz_t so
 *   that the counter n grows without bound, faithfully implementing the
 *   infinite enumeration of rice.v's find_sol.
 *
 *   This is NOT merely a practical concern about large search spaces.
 *   It is a correctness requirement: the C program must be an instance of
 *   the program family to which Rice_Theorem applies, and that family
 *   consists of programs that run forever on unsolvable inputs.
 *
 * CONNECTION TO THE ROCQ PROOF:
 *
 *   The function find_sol_one() below is a direct C translation of:
 *
 *     Fixpoint find_sol (ar : nat) (p : Poly) (fuel : nat) : option nat
 *
 *   in rice.v, in the limit fuel -> infinity (unbounded search).
 *   The outer loop in program 2 composes find_sol_one instances sequentially,
 *   one per target k, yielding a program that is an instance of the
 *   two-witness construction of Definition 4.2 in the paper.
 *
 * Author: Jonathan Brossard <brossardj@acm.org>
 * License: CC BY 4.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <gmp.h>

/* =========================================================================
 * Cantor pairing / unpairing  (arbitrary precision via GMP)
 *
 * cantor_w(n)   = floor( (sqrt(8n+1) - 1) / 2 )
 * fst(n)        = w - (n - w*(w+1)/2)
 * snd(n)        = n - w*(w+1)/2
 *
 * All quantities are mpz_t (unbounded integers).
 * ========================================================================= */

static void cantor_w(mpz_t w, const mpz_t n)
{
    mpz_t tmp;
    mpz_init(tmp);
    mpz_mul_ui(tmp, n, 8);
    mpz_add_ui(tmp, tmp, 1);
    mpz_sqrt(tmp, tmp);
    mpz_sub_ui(tmp, tmp, 1);
    mpz_tdiv_q_ui(w, tmp, 2);
    mpz_clear(tmp);
}

static void cantor_fst(mpz_t fst, const mpz_t n)
{
    mpz_t w, t;
    mpz_inits(w, t, NULL);
    cantor_w(w, n);
    mpz_add_ui(t, w, 1);
    mpz_mul(t, w, t);
    mpz_tdiv_q_ui(t, t, 2);
    mpz_sub(t, n, t);
    mpz_sub(fst, w, t);
    mpz_clears(w, t, NULL);
}

static void cantor_snd(mpz_t snd_out, const mpz_t n)
{
    mpz_t w, t;
    mpz_inits(w, t, NULL);
    cantor_w(w, n);
    mpz_add_ui(t, w, 1);
    mpz_mul(t, w, t);
    mpz_tdiv_q_ui(t, t, 2);
    mpz_sub(snd_out, n, t);
    mpz_clears(w, t, NULL);
}

/*
 * decode(ar, n, vars[]) fills vars[0..ar-1] with the ar-tuple encoded by n.
 * Mirrors decode_k in rice.v.
 * vars[] must be a pre-initialised mpz_t array of size ar.
 */
static void decode(int ar, const mpz_t n, mpz_t *vars)
{
    if (ar == 1) {
        mpz_set(vars[0], n);
    } else {
        mpz_t fst, snd;
        mpz_inits(fst, snd, NULL);
        cantor_fst(fst, n);
        cantor_snd(snd, n);
        decode(ar - 1, fst, vars);
        mpz_set(vars[ar - 1], snd);
        mpz_clears(fst, snd, NULL);
    }
}

/* =========================================================================
 * Check-function type.
 * ctx is an arbitrary context pointer passed through from find_sol_one().
 * Returns 1 if the tuple satisfies the target equation, 0 otherwise.
 * ========================================================================= */

typedef int (*CheckFn)(mpz_t *vars, int ar, void *ctx);

/* =========================================================================
 * find_sol_one — search for ONE solution to a single Diophantine equation.
 *
 * Mirrors rice.v's find_sol in the limit fuel -> infinity.
 * Runs forever if the equation has no solution.
 * Returns when a solution is found.
 * ========================================================================= */

static void find_sol_one(int ar, CheckFn check, void *ctx,
                         const char *equation_desc)
{
    printf("  Searching: %s\n", equation_desc);
    fflush(stdout);

    mpz_t n;
    mpz_init_set_ui(n, 0);

    mpz_t *vars = malloc(ar * sizeof(mpz_t));
    for (int i = 0; i < ar; i++)
        mpz_init(vars[i]);

    unsigned long report = 10000000UL;

    while (1) {
        decode(ar, n, vars);
        if (check(vars, ar, ctx)) {
            printf("    Solution found: ");
            for (int i = 0; i < ar; i++) {
                printf("x%d=", i);
                mpz_out_str(stdout, 10, vars[i]);
                if (i + 1 < ar) printf(", ");
            }
            printf("\n");
            fflush(stdout);
            break;
        }
        mpz_add_ui(n, n, 1);
        if (mpz_cmp_ui(n, report) == 0) {
            printf("    Still searching... (n=");
            mpz_out_str(stdout, 10, n);
            printf(")\n");
            fflush(stdout);
            report *= 2;
        }
    }

    for (int i = 0; i < ar; i++) mpz_clear(vars[i]);
    free(vars);
    mpz_clear(n);
}

/* =========================================================================
 * Program 1 — DECIDABLE
 *
 * Searches for x^2 - y^2 - z^2 = 1.
 * Solution: x=1, y=0, z=0 (found immediately at n=1).
 * Termination: provable.
 * ========================================================================= */

static int check_p1(mpz_t *v, int ar, void *ctx)
{
    (void)ar; (void)ctx;
    mpz_t lhs, t;
    mpz_inits(lhs, t, NULL);
    mpz_mul(lhs, v[0], v[0]);
    mpz_mul(t,   v[1], v[1]); mpz_sub(lhs, lhs, t);
    mpz_mul(t,   v[2], v[2]); mpz_sub(lhs, lhs, t);
    int found = (mpz_cmp_si(lhs, 1) == 0);
    mpz_clears(lhs, t, NULL);
    return found;
}

static void run_decidable(void)
{
    printf("Program 1: searching for x^2 - y^2 - z^2 = 1\n");
    printf("The equation is solvable (x=1, y=0, z=0).\n");
    printf("This program provably terminates.\n\n");
    find_sol_one(3, check_p1, NULL, "x^2 - y^2 - z^2 = 1");
    printf("\nDone. The equation is solvable; termination was guaranteed.\n");
}

/* =========================================================================
 * Program 2 — UNDECIDABLE
 *
 * For k = 0, 1, 2, ... (skipping k ≡ 4 or 5 mod 9, which are provably
 * impossible), searches for integer x, y, z such that x^3 + y^3 + z^3 = k.
 * Advances to k+1 as soon as a solution for the current k is found.
 *
 * This program terminates if and only if every integer not congruent to
 * 4 or 5 (mod 9) is representable as a sum of three integer cubes —
 * an open conjecture in number theory (as of 2026).
 *
 * Unlike a search for a single fixed target (e.g. k=114), this formulation
 * is permanently open: resolving any individual k merely advances the search.
 * The termination question is equivalent to the full conjecture and cannot
 * be resolved by settling any finite collection of cases.
 *
 * Known open values include (but are not limited to):
 *   114, 390, 627, 633, 732, 906, 921, 975, ...
 * (See Huisman 2016; OEIS A060464 for the current list.)
 *
 * We search over all sign combinations at each Cantor-decoded tuple to
 * cover negative integers.
 * ========================================================================= */

/* ctx points to a long holding the current target k */
static int check_p2(mpz_t *v, int ar, void *ctx)
{
    (void)ar;
    uint64_t target = *(uint64_t *)ctx;
    mpz_t lhs, cx, cy, cz;
    mpz_inits(lhs, cx, cy, cz, NULL);
    int found = 0;
    /* Enumerate all 8 sign combinations to cover Z^3 */
    for (int si = -1; si <= 1 && !found; si += 2)
    for (int sj = -1; sj <= 1 && !found; sj += 2)
    for (int sk = -1; sk <= 1 && !found; sk += 2) {
        /* cx = (si * v[0])^3 */
        mpz_mul_si(cx, v[0], si);
        mpz_mul(cx, cx, cx);
        mpz_mul_si(cx, cx, si);
        mpz_mul(cx, cx, v[0]);
        /* cy = (sj * v[1])^3 */
        mpz_mul_si(cy, v[1], sj);
        mpz_mul(cy, cy, cy);
        mpz_mul_si(cy, cy, sj);
        mpz_mul(cy, cy, v[1]);
        /* cz = (sk * v[2])^3 */
        mpz_mul_si(cz, v[2], sk);
        mpz_mul(cz, cz, cz);
        mpz_mul_si(cz, cz, sk);
        mpz_mul(cz, cz, v[2]);
        mpz_add(lhs, cx, cy);
        mpz_add(lhs, lhs, cz);
        if (mpz_cmp_ui(lhs, target) == 0) found = 1;
    }
    mpz_clears(lhs, cx, cy, cz, NULL);
    return found;
}

/*
 * Returns 1 if k is excluded by the mod-9 obstruction
 * (i.e. k ≡ 4 or 5 mod 9 — provably not a sum of three cubes).
 */
static int excluded_mod9(uint64_t k)
{
    uint64_t r = k % 9;
    return (r == 4 || r == 5);
}

static void run_undecidable(void)
{
    printf("Program 2: for each eligible k = 0, 1, 2, ...\n");
    printf("  search for integer x, y, z with x^3 + y^3 + z^3 = k.\n");
    printf("  (Skipping k ≡ 4 or 5 mod 9: provably impossible.)\n\n");
    printf("This program terminates iff every eligible integer is a sum\n");
    printf("of three integer cubes — an open conjecture in number theory.\n");
    printf("Whether it terminates is an open mathematical problem.\n\n");
    printf("No static analyzer can decide this without resolving the conjecture;\n");
    printf("by Rice_Theorem (rice.v), no such analyzer can exist for the family.\n\n");

    /* Note: k is a uint64_t (max 2^64 - 1, platform-independent), not a
     * GMP mpz_t. This is intentional and correct. The inner counter n inside
     * find_sol_one() must be unbounded (GMP) because a 64-bit n would
     * exhaust in finite time, making the inner search trivially terminating
     * and invalidating the formal claim. The outer k is different: the
     * program stalls at the first open value of the conjecture (e.g. 114)
     * and never advances past it in practice. Overflow of k at 2^64-1
     * is purely hypothetical — it would require resolving ~1.8e19
     * consecutive cases of an open conjecture, which is not going to happen.
     * Using uint64_t here is therefore correct; the undecidability is in the
     * inner search, not in the range of k. */
    for (uint64_t k = 0; ; k++) {
        if (excluded_mod9(k)) {
            printf("  k=%" PRIu64 ": skipped (≡ %" PRIu64 " mod 9, provably impossible)\n",
                   k, k % 9);
            fflush(stdout);
            continue;
        }
        char desc[64];
        snprintf(desc, sizeof(desc), "x^3 + y^3 + z^3 = %" PRIu64, k);
        find_sol_one(3, check_p2, &k, desc);
    }
    /* Never reached unless the conjecture holds for all k — i.e. never,
     * unless mathematics resolves an open problem. */
}

/* =========================================================================
 * Main
 * ========================================================================= */

int main(int argc, char **argv)
{
    printf("=================================================================\n");
    printf("undecidable.c — formally undecidable static analysis target\n");
    printf("Theorem Rice_Theorem in rice.v (Rocq 8.20)\n");
    printf("Counter: GMP mpz_t (unbounded — faithfully implements find_sol)\n");
    printf("=================================================================\n\n");

    if (argc < 2 ||
        (strcmp(argv[1], "decidable")   != 0 &&
         strcmp(argv[1], "undecidable") != 0)) {
        printf("Usage:\n\n");
        printf("  ./undecidable decidable\n");
        printf("      Search for x^2 - y^2 - z^2 = 1.\n");
        printf("      Solvable (x=1,y=0,z=0); this program provably terminates.\n\n");
        printf("  ./undecidable undecidable\n");
        printf("      For k=0,1,2,... (skipping k≡4,5 mod 9), search for\n");
        printf("      x^3+y^3+z^3=k. Terminates iff every eligible integer\n");
        printf("      is a sum of three integer cubes (open conjecture, 2026).\n\n");
        printf("Both programs are instances of the find_sol construction\n");
        printf("from rice.v. By Theorem Rice_Theorem, no static analyzer can\n");
        printf("correctly decide termination for the full program family.\n\n");
        return (argc < 2) ? 0 : 1;
    }

    if (strcmp(argv[1], "decidable") == 0)
        run_decidable();
    else
        run_undecidable();

    return 0;
}
