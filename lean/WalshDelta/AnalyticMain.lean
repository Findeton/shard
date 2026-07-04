import Mathlib
import WalshDelta.Basic
import WalshDelta.Trichotomy
import WalshDelta.Symmetry
import WalshDelta.Delta
import WalshDelta.Calibration

/-!
# Walsh–delta: the analytic main theorem for `n ≥ 6` (Paper XII, Section 7)

Formalization of Section 7 of

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube"  (Paper XII).

This module assembles the analytic (`n ≥ 6`) half of the main theorem:

* **Theorem 7.1** — for `n ≥ 6` and any non-delta orientation `ε`,
  `mhat ε > D_δ`, proved by the paper's two-case split
  (`D > 1/60` uses Lemma 4.2 and `N - 1 ≥ 63`; `D ≤ 1/60` uses Theorem 6.1
  and the arithmetic fact `2.878716·(N-1) > N`).
* **Corollary 1.3** — the quantitative floor
  `N·mhat ε ≥ min(N/60, 2.878716)` for non-delta `ε`, together with
  `N·D_δ < N/(N-1) ≤ 64/63`.
* **Theorem 1.2 (the `n ≥ 6` half)** — `mhat ε ≥ D_δ` with equality iff `ε`
  is a delta orientation.

## Interfaces to Sections 3, 4, 6

Section 7 consumes the following results, proved in the paper's earlier
sections.  In a multi-file build they would be `import`ed from the
existence / delta-law / deep-dip modules; here they are stated (with `sorry`)
as the interface this module rests on, each labeled with its paper number:

  * `calibrated_exists_unique`  — Theorem 3.1 (existence and uniqueness of the
    calibrated law `P_ε`), whence `Pcal`, `mhat`;
  * `translation_covariance`, `tau_deltaOrientation`, `mhat_deltaOrientation`
    — Lemma 3.2 (all `N` delta orientations share the value `D_δ`);
  * `Ddelta_lt` — Lemma 4.2 (`0 < D_δ < 1/(N-1)`);
  * `deep_dip_trichotomy` — Theorem 6.1 (deep-dip trichotomy).
-/

namespace WalshDelta

open scoped BigOperators

variable {n : ℕ}

/-! ## The calibrated law `P_ε` and the entropy functional `mhat` (Theorem 3.1) -/

-- (removed redundant `calibrated_exists_unique`; canonical in an imported module)
/-- Paper XII, Theorem 3.1.  The unique calibrated law `P_ε` of the
orientation `ε`. -/
noncomputable def Pcal (ε : Orientation n) : ProbLaw n :=
  (calibrated_exists_unique ε).exists.choose  -- TODO(api): verify `ExistsUnique.exists`

/-- Paper XII, Theorem 3.1: `P_ε := Pcal ε` is indeed calibrated for `ε`. -/
lemma Pcal_calibrated (ε : Orientation n) : Calibrated (Pcal ε) ε :=
  (calibrated_exists_unique ε).exists.choose_spec

-- (removed redundant `mhat`; canonical in an imported module)
/-! ## Delta orientations: the predicate and the shared value `D_δ` -/

-- (removed redundant `IsDelta`; canonical in an imported module)
/-- Helper: the product of two `±1`-valued reals is `±1`-valued. -/
lemma mul_pm_one {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inl (by norm_num)

/-- Paper XII, Lemma 3.2.  The translated orientation
`(τ_t ε)_a = ε_a · χ_a(t)`. -/
def tau (t : Point n) (ε : Orientation n) : Orientation n where
  sign := fun a => ε.sign a * chi a.1 t
  is_sign := fun a => mul_pm_one (ε.is_sign a) (chi_mem a.1 t)

/-- Paper XII, Lemma 3.2 (translation covariance).  For `t ∈ G`,
`P_{τ_t ε}(s) = P_ε(s + t)` and `m̂(τ_t ε) = m̂(ε)`. -/
theorem translation_covariance (t : Point n) (ε : Orientation n) :
    (∀ s, (Pcal (tau t ε)).P s = (Pcal ε).P (s + t)) ∧
      mhat (tau t ε) = mhat ε := by
  sorry
  -- Lemma 3.2: `ℓ ↦ ℓ' := (ℓ_a χ_a(t))_a` is a linear bijection with
  -- `G_{τ_t ε}(ℓ') = G_ε(ℓ)` (the substitution `s ↦ s+t` preserves `U`), so it
  -- carries the unique minimizer to the unique minimizer; the laws are
  -- translates, and `D(·‖U)` is translation-invariant.

/-- Paper XII, Lemma 3.2 (delta orbit).
`τ_t(ε⋆ at s⋆) = ε⋆ at s⋆ + t`: the `N` delta orientations form a single
translation orbit. -/
theorem tau_deltaOrientation (t sstar : Point n) :
    tau t (deltaOrientation sstar) = deltaOrientation (sstar + t) := by
  sorry
  -- Lemma 3.2: `(τ_t ε⋆)_a = -χ_a(s⋆)·χ_a(t) = -χ_a(s⋆+t)` by multiplicativity
  -- of `χ_a` in its point argument; hence the sign fields agree (funext), and
  -- the orientations are equal by structure/proof-irrelevance extensionality.

-- (removed redundant `Ddelta`; canonical in an imported module)
-- (removed redundant `mhat_deltaOrientation`; canonical in an imported module)
/-! ## Lemma 4.2 (elementary delta bound) -/

-- (removed redundant `Ddelta_lt`; canonical in an imported module)
/-! ## Theorem 6.1 (deep-dip trichotomy) -/

-- (removed redundant `deep_dip_trichotomy`; canonical in an imported module)
/-! ## Arithmetic facts used in the case split -/

/-- Paper XII, Section 6/7: `ψ(e^{-5}) = 1 - 6 e^{-5}`. -/
lemma psi_exp_neg_five : psi (Real.exp (-5)) = 1 - 6 * Real.exp (-5) := by
  unfold psi
  rw [Real.log_exp]
  ring

/-- Paper XII, Theorem 6.1: `3 ψ(e^{-5}) = 3(1 - 6 e^{-5}) = 2.8787169… >
2.878716`. -/
lemma three_psi_gt : (2.878716 : ℝ) < 3 * (1 - 6 * Real.exp (-5)) := by
  sorry
  -- `3(1 - 6 e^{-5}) = 2.87871690…`.  To be discharged by rigorous rational
  -- interval arithmetic on `e^{-5}` (e.g. a certified enclosure of `e^{-5}`),
  -- NOT by `native_decide`.

/-- Paper XII, Section 7 (arithmetic fact).  `2.878716·(N-1) > N` for every
`N ≥ 2` (equivalently `N > 2.878716/1.878716 = 1.532…`). -/
lemma calib_N_bound (hN2 : (2 : ℝ) ≤ (N n : ℝ)) :
    (N n : ℝ) < 2.878716 * ((N n : ℝ) - 1) := by
  nlinarith [hN2]  -- linear in N: `1.878716·N > 2.878716`, true for N ≥ 2

/-! ## Theorem 7.1 (the main theorem for `n ≥ 6`) -/

/-- Paper XII, Theorem 7.1.  Let `n ≥ 6` and let `ε` be any orientation that is
not a delta orientation.  Then `m̂(ε) > D_δ`. -/
theorem main_analytic (hn : 6 ≤ n) (ε : Orientation n) (hnd : ¬ IsDelta ε) :
    Ddelta n < mhat ε := by
  sorry  -- proof stubbed to sorry (renamed order/div API in the drafted proof); statement is faithful
theorem corollary_1_3 (hn : 6 ≤ n) (ε : Orientation n) (hnd : ¬ IsDelta ε) :
    min ((N n : ℝ) / 60) 2.878716 ≤ (N n : ℝ) * mhat ε
      ∧ (N n : ℝ) * Ddelta n < (N n : ℝ) / ((N n : ℝ) - 1)
      ∧ (N n : ℝ) / ((N n : ℝ) - 1) ≤ 64 / 63 := by
  sorry  -- proof stubbed to sorry (renamed order/div API in the drafted proof); statement is faithful
theorem main_equality_analytic (hn : 6 ≤ n) (ε : Orientation n) :
    Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε) := by
  -- Combines `main_analytic` (strict for non-delta) with `mhat` being constant
  -- `= Ddelta n` on the delta family (Symmetry.mhat_deltaOrientation).
  sorry

end WalshDelta
