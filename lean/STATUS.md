# STATUS — WalshDelta formalization

**One line:** the **whole library compiles and links** against Mathlib (Lean
`v4.32.0-rc1`) — `lake build` succeeds with **0 errors** — and the headline
`WalshDelta.theorem_1_2` is a **complete, machine-checked assembly** that reduces
to two halves. The definitions and every theorem *statement* are therefore
kernel-verified as well-formed; the remaining work is the **93 `sorry` proof
leaves** (the actual mathematical content).

Date: 2026-07-03. Verified with `lake build` against a locally built Mathlib.

## What is verified now

- **`lake build` links the entire library** (all 8 modules, one namespace,
  canonical shared definitions). 0 elaboration errors.
- **`theorem_1_2` is proved as an assembly** (its own proof body has no
  `sorry`): it case-splits on `n` and defers to `AnalyticMain.main_equality_analytic`
  (`n ≥ 6`, analytic) and `Certified.theorem_8_3` (`2 ≤ n ≤ 5`, certified
  computation). Its axiom dependency is transparent:
  ```
  #print axioms WalshDelta.theorem_1_2
  --> [propext, sorryAx, Classical.choice, Quot.sound]
  ```
  i.e. the three standard Mathlib axioms **plus `sorryAx`** — the honest marker
  that the two halves are still `sorry`. Discharging the `sorry`s removes
  `sorryAx` and makes the whole theorem kernel-checked.
- Every definition and theorem statement type-checks — which is the load-bearing
  part of "bug-free": a formal proof is only as meaningful as its statement.

## What is not done

**64 `sorry`s** remain (29 discharged and `lake build`-verified; see `SORRIES.md`).  Nothing is claimed proved
unless Lean accepts it; `#print axioms` will show `sorryAx` until they are gone.

Recently discharged (this pass, all `lake build`-verified): the Walsh
orthogonality core (`Delta.sum_chi`, `sum_nonzero_chi`), the delta-polynomial root
theory (`Delta.deltaPoly_strictMonoOn`, `deltaPoly_pos_at_bound`,
`uStar_exists_unique` by IVT — which also clears `uStar_spec`/`uStar_pos`/
`deltaPoly_uStar`/`uStar_lt` transitively — and `tauOrient_deltaOrientation`), the
moment-matrix positive-semidefiniteness (`Certified.secondMomentMatrix_psd`,
`covMatrix_psd` via Cauchy–Schwarz, `covMatrix_le_secondMoment`, plus the reusable
closed forms `quadForm_secondMomentMatrix`, `sum_v_xcoord`, `quadForm_covMatrix_eq`),
and the `GL(n,2)`/translation kinematics (`Symmetry.dotZ2_mulVec`,
`glTransInv_mulVec_ne_zero`, `glOrient_one`, `delta_injective`, `delta_glAction`),
plus `Trichotomy.log_abs_le_two_abs_sub_one`.

The remaining 64 are the three research frontiers plus what depends on them: the
**convex-analysis core** (`Calibration` — `G_ε` strictly convex + coercive ⇒ unique
minimizer = calibrated law; this gates `Delta.exists_unique_calibrated`,
`calLaw_tauOrient`, `mhat_tauOrient`, `calibrated_deltaLaw`, `Ddelta_*`, and the four
`Symmetry` calibrated-law covariance theorems), the **analytic frontier**
(`Trichotomy`/`AnalyticMain` quantitative deep-dip bounds + the tight numeric
constants `e^{-5}`, `2.878716`, `64/63` — needing rigorous interval arithmetic, not
`norm_num` on transcendentals), and the **certified frontier** (`Certified` §8
Newton–Kantorovich over the 176-orbit Γ₅ transversal, plus the spectral
`opNorm_le_trace_of_psd`).

## How it was produced

Statements were extracted from paper XII (`../papers/paper-XII-walsh-delta.md`),
formalized module-by-module (a multi-agent drafting pass), then **compiled and
iterated against Mathlib**: mechanical elaboration errors were fixed
(`noncomputable`, a stray `open … in`, a renamed `EqvGen`, renamed order/division
lemmas), and — the substantive integration step — the shared objects `mhat`,
`Ddelta`, `IsDelta` (originally redeclared in up to 5 modules via different
calibrated-law intermediates) were **unified onto single canonical homes**
(`mhat`,`Ddelta` in `Calibration`; `IsDelta` in `Basic`), the duplicates deleted
and re-imported, until the whole library linked. A handful of drafted proofs that
depended on the old private definitions were reduced to `sorry` (statements
kept).

## Inventory (per module — all compile; the library links)

| Module | Formalizes (paper) | `sorry` |
|---|---|---:|
| `Basic` | §1.1 objects; §2 Pinsker (2.1) + ψ (2.2); canonical `IsDelta` | 1 |
| `Calibration` | §3 Thm 3.1; canonical `mhat`, `Ddelta` | 14 |
| `Symmetry` | §3 Lemmas 3.2 / 3.3 (covariance) | 4 |
| `Delta` | §1.2 + §4 Prop 4.1 (delta law), Lemma 4.2 | 10 |
| `Trichotomy` | §5 apparatus + §6 Thm 6.1 (deep-dip trichotomy) | 13 |
| `AnalyticMain` | §7 Thm 7.1 / main theorem n≥6 / Cor 1.3 | 6 |
| `Certified` | §8 Lemmas 8.1/8.2 + Thm 8.3 (2≤n≤5, 176-orbit) | 15 |
| `Main` | **Thm 1.2** (assembled, proof body sorry-free) + Cor 1.3 | 1 |
| **total** | | **64** |

(`sorry` counts are the tactic leaves; a couple more appear inside `def` bodies
for scaffolding — e.g. `Certified.cGl`'s nonzero-preservation.)

## Remaining work — discharge the remaining `sorry`s

Roughly in order:
1. **Standard Mathlib territory:** `Basic` (χ homomorphism, Pinsker, ψ facts),
   `Calibration` (convexity/coercivity of `Gobj`), `Symmetry` (covariance),
   `Delta` (the two-level law + `u⋆` root).
2. **The analytic frontier** (`Trichotomy`, `AnalyticMain`): the quantitative
   inequalities — rigorous bounds on `e^{-5}`, `ψ`, `2.878716`, `64/63` — via
   Mathlib `Real.log`/`Real.exp` bounds + `norm_num` + interval reasoning.
3. **The certified frontier** (`Certified.theorem_8_3`): discharge by **exact
   rational / interval arithmetic** through the Newton–Kantorovich certificates
   (`Lemma 8.1` radius, `Lemma 8.2` transfer) over the **176-orbit Γ₅ transversal**
   (`Symmetry` reduces 2³¹ orientations to 176). `native_decide` is deliberately
   **not** used (trust base + soundness); reflect the finite computation into
   `ℚ`/interval arithmetic with the Burnside completeness checksum formalized.

At zero `sorry`, `#print axioms WalshDelta.theorem_1_2` shows only
`[propext, Classical.choice, Quot.sound]` and the theorem is kernel-checked.

## Reproduce

```
cd shard/lean                 # Mathlib pinned via lake-manifest.json; toolchain v4.32.0-rc1
lake build                    # links the whole library, 0 errors (80 sorry warnings)
lake env lean -c 'import WalshDelta; #print axioms WalshDelta.theorem_1_2'
```

See `BLUEPRINT.md` for the module graph, the name↔paper mapping, and the Mathlib
pieces this leans on. This is a good blueprint-driven target for the
Lean/Mathlib community (PFR/FLT-style).
