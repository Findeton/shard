import Mathlib
import WalshDelta.Basic
import WalshDelta.Symmetry
import WalshDelta.Calibration

/-!
# Walsh–delta: the certified computation for `2 ≤ n ≤ 5` (Paper XII, Section 8)

Formalization of Section 8 of

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube"  (Paper XII).

This module states the two a-posteriori certification lemmas (Lemma 8.1, the
error radius; Lemma 8.2, the entropy-transfer bound), the finite main theorem
(Theorem 8.3, `2 ≤ n ≤ 5`), and the `Γ_n`-orbit reduction interface used for
`n = 5` (Section 8.3).

## Note on module boundaries

The Section-3/4/5 objects that Section 8 rests on — the log-partition `F`, the
Gibbs mean `x(ℓ)`, the convex objective `G_ε` (Theorem 3.1), the minimizer
`ℓ⋆`, the entropy value `m̂(ε)`, the relative-entropy functional `𝒟(ℓ)`, and the
delta reference `D_δ` — would in a full development live in dedicated modules
(`WalshDelta.Convex`, `WalshDelta.Delta`, `WalshDelta.Symmetry`).  Those modules
do not yet exist, so to keep this file self-contained and its statements
faithful we introduce those objects here, each with a docstring citing the
paper.  None of them redefine an object exported by `WalshDelta.Basic`; they
reuse `Basic`'s `Point`, `chi`, `EU`, `NonzeroMask`, `Orientation`,
`deltaOrientation`, etc. verbatim.
-/

namespace WalshDelta

open scoped BigOperators

variable {n : ℕ}

/-! ## Section-3 substrate: `F`, `x(ℓ)`, `G_ε`, the minimizer `ℓ⋆`, and `m̂` -/

/-- Paper XII, Section 3.  The linear tilt `∑_{a≠0} ℓ_a χ_a(s)` (the Section-3
parametrization by `ℓ` directly, related to Basic's `tilt` by `ℓ_a = h_a ε_a`). -/
def linComb (ℓ : NonzeroMask n → ℝ) (s : Point n) : ℝ :=
  ∑ a : NonzeroMask n, ℓ a * chi a.1 s

/-- Paper XII, Section 3.  The Gibbs weight `exp(∑_a ℓ_a χ_a(s))` (unnormalized
density of `P_ℓ` w.r.t. uniform). -/
noncomputable def gibbsWeight (ℓ : NonzeroMask n → ℝ) (s : Point n) : ℝ :=
  Real.exp (linComb ℓ s)

/-- Paper XII, Section 3.  The partition sum `Z(ℓ) = ∑_s exp(∑_a ℓ_a χ_a(s))`. -/
noncomputable def Zpart (ℓ : NonzeroMask n → ℝ) : ℝ := ∑ s, gibbsWeight ℓ s

/-- `Z(ℓ) > 0` (a sum of exponentials over the nonempty cube). -/
lemma Zpart_pos (ℓ : NonzeroMask n → ℝ) : 0 < Zpart ℓ := by
  have : Nonempty (Point n) := inferInstance
  apply Finset.sum_pos
  · intro s _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Paper XII, Section 3.  The log-partition function
`F(ℓ) = log 𝔼_U exp(∑_{a≠0} ℓ_a χ_a)`. -/
noncomputable def Fpart (ℓ : NonzeroMask n → ℝ) : ℝ :=
  Real.log (EU (fun s => Real.exp (linComb ℓ s)))

/-- Paper XII, Section 3.  The Gibbs mean of a character,
`x_a(ℓ) = 𝔼_{P_ℓ}[χ_a] = ∂F/∂ℓ_a`. -/
noncomputable def xcoord (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) : ℝ :=
  (∑ s, gibbsWeight ℓ s * chi a.1 s) / Zpart ℓ

/-- Paper XII, Section 3, Theorem 3.1.  The strictly convex objective
`G_ε(ℓ) = F(ℓ) + ∑_{a≠0} e^{-ε_a ℓ_a}`. -/
noncomputable def Gobj (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) : ℝ :=
  Fpart ℓ + ∑ a : NonzeroMask n, Real.exp (- ε.sign a * ℓ a)

/-- Paper XII, Theorem 3.1 (existence and uniqueness).  For every orientation
`ε`, the objective `G_ε` has a unique global minimizer on `ℝ^{N-1}`.  (Proved in
Section 3 via smoothness + strict convexity + coercivity; the analytic proof
belongs to the convexity module.) -/
theorem exists_unique_minimizer (ε : Orientation n) :
    ∃! ℓ : NonzeroMask n → ℝ, ∀ m, Gobj ε ℓ ≤ Gobj ε m := by
  sorry
  -- `G_ε` is smooth, strictly convex (`∇²G_ε ⪰ diag(e^{-ε_a ℓ_a}) ≻ 0`), and
  -- coercive (`F(tv) ≥ tμ(v) - log N → ∞`), hence attains a unique minimum.
  -- Cf. Theorem 3.1.

/-- Paper XII, Theorem 3.1.  The unique minimizer `ℓ⋆(ε)` of `G_ε`. -/
noncomputable def lstar (ε : Orientation n) : NonzeroMask n → ℝ :=
  (exists_unique_minimizer ε).exists.choose

/-- `ℓ⋆(ε)` is a global minimizer of `G_ε` (Theorem 3.1). -/
theorem lstar_isMinimizer (ε : Orientation n) :
    ∀ m, Gobj ε (lstar ε) ≤ Gobj ε m :=
  (exists_unique_minimizer ε).exists.choose_spec

/-- Paper XII, Section 8.2.  The relative-entropy functional
`𝒟(ℓ) := D(P_ℓ ‖ U) = ⟨ℓ, x(ℓ)⟩ - F(ℓ)`. -/
noncomputable def Dcal (ℓ : NonzeroMask n → ℝ) : ℝ :=
  (∑ a : NonzeroMask n, ℓ a * xcoord ℓ a) - Fpart ℓ

-- (removed redundant `mhat`; canonical in an imported module)
-- (removed redundant `Ddelta`; canonical in an imported module)
/-- Paper XII, Lemma 3.2.  All `N` delta orientations share the value `D_δ`. -/
theorem Ddelta_eq (sstar : Point n) : mhat (deltaOrientation sstar) = Ddelta n := by
  sorry
  -- Translation covariance (Lemma 3.2): the delta orientations form one
  -- translation orbit and `m̂` is translation-invariant.  Cf. Lemma 3.2.

-- (removed redundant `IsDelta`; canonical in an imported module)
/-- The distinguished `deltaOrientation` at `s⋆` satisfies `IsDelta`. -/
lemma isDelta_deltaOrientation (sstar : Point n) :
    IsDelta (deltaOrientation sstar) :=
  ⟨sstar, rfl⟩

/-! ## The `ℓ²`-geometry on `ℝ^{N-1}` -/

/-- Paper XII, Section 8.  The Euclidean (`ℓ²`) norm on `ℝ^{N-1}`, indexed by
nonzero masks: `‖v‖₂ = √(∑_a v_a²)`. -/
noncomputable def l2norm (v : NonzeroMask n → ℝ) : ℝ := Real.sqrt (∑ a, (v a) ^ 2)

/-! ## The gradient of `G_ε`, and the Hessian of `F` -/

/-- Paper XII, Section 3 / Section 8.1.  The gradient of `G_ε`, componentwise:
`(∇G_ε)_a = x_a(ℓ) - ε_a e^{-ε_a ℓ_a}`. -/
noncomputable def gradG (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) : ℝ :=
  xcoord ℓ a - ε.sign a * Real.exp (- ε.sign a * ℓ a)

/-- Paper XII, Section 3.  The second moment `𝔼_{P_ℓ}[χ_a χ_b]`. -/
noncomputable def secondMoment (ℓ : NonzeroMask n → ℝ) (a b : NonzeroMask n) : ℝ :=
  (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) / Zpart ℓ

/-- Paper XII, Section 3.  The Hessian `∇²F(ℓ) = Cov_{P_ℓ}(χ)`, with entries
`𝔼_{P_ℓ}[χ_a χ_b] - x_a x_b`. -/
noncomputable def covMatrix (ℓ : NonzeroMask n → ℝ) :
    Matrix (NonzeroMask n) (NonzeroMask n) ℝ :=
  fun a b => secondMoment ℓ a b - xcoord ℓ a * xcoord ℓ b

/-- Paper XII, Section 8.1 (proof of Lemma 8.2).  The uncentered second-moment
matrix `𝔼_{P_ℓ}[χ χᵀ]`. -/
noncomputable def secondMomentMatrix (ℓ : NonzeroMask n → ℝ) :
    Matrix (NonzeroMask n) (NonzeroMask n) ℝ :=
  fun a b => secondMoment ℓ a b

/-- The quadratic form `vᵀ H v = ∑_{a,b} v_a H_{ab} v_b` associated to a matrix
`H`; used to express operator-norm bounds without invoking the operator-norm
API directly. -/
def quadForm (H : Matrix (NonzeroMask n) (NonzeroMask n) ℝ)
    (v : NonzeroMask n → ℝ) : ℝ :=
  ∑ a, ∑ b, v a * H a b * v b

/-! ### Elementary character algebra used below -/

/-- `χ_a(s)² = 1` since every Walsh character is `±1`-valued. -/
lemma chi_mul_self (a s : Point n) : chi a s * chi a s = 1 := by
  rcases chi_mem a s with h | h <;> rw [h] <;> norm_num

/-- Paper XII, Section 8.1.  The diagonal second moment is `𝔼_{P_ℓ}[χ_a²] = 1`. -/
lemma secondMoment_diag (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) :
    secondMoment ℓ a a = 1 := by
  have hchi : ∀ s, gibbsWeight ℓ s * chi a.1 s * chi a.1 s = gibbsWeight ℓ s := by
    intro s; rw [mul_assoc, chi_mul_self]; ring
  unfold secondMoment
  simp only [hchi]
  exact div_self (Zpart_pos ℓ).ne'

/-- Paper XII, Section 1.1.  There are exactly `N - 1` nonzero masks. -/
lemma card_nonzeroMask (n : ℕ) : Fintype.card (NonzeroMask n) = N n - 1 := by
  show Fintype.card {a : Point n // a ≠ 0} = N n - 1
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_point]
  -- TODO(api): confirm `Fintype.card_subtype_compl` and `Fintype.card_subtype_eq`.

/-- Paper XII, Section 8.1 (proof of Lemma 8.2).  `tr 𝔼[χχᵀ] = ∑_{a≠0} 1
= |{a≠0}|`. -/
lemma trace_secondMomentMatrix (ℓ : NonzeroMask n → ℝ) :
    Matrix.trace (secondMomentMatrix ℓ) = (Fintype.card (NonzeroMask n) : ℝ) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, secondMomentMatrix, secondMoment_diag]
  simp [Finset.card_univ]
  -- TODO(api): confirm `Matrix.trace` unfolds to `∑ i, diag i` and `Matrix.diag_apply`.

/-- Paper XII, Section 8.1 (proof of Lemma 8.2).  `tr 𝔼[χχᵀ] = N - 1`. -/
lemma trace_secondMomentMatrix_eq (ℓ : NonzeroMask n → ℝ) :
    Matrix.trace (secondMomentMatrix ℓ) = (N n : ℝ) - 1 := by
  rw [trace_secondMomentMatrix, card_nonzeroMask, Nat.cast_sub (N_pos n), Nat.cast_one]

/-! ### Positive semidefiniteness and symmetry of the moment matrices -/

/-- Paper XII, Section 3.  The weighted mean `∑_a v_a x_a(ℓ)` in closed form:
`= (∑_s w_ℓ(s)(∑_a v_a χ_a(s)))/Z(ℓ)`. -/
lemma sum_v_xcoord (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    (∑ a : NonzeroMask n, v a * xcoord ℓ a)
      = (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s)) / Zpart ℓ := by
  have numX : (∑ a : NonzeroMask n, v a * (∑ s, gibbsWeight ℓ s * chi a.1 s))
      = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun a _ => by ring))
  have Xdist : (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s)) / Zpart ℓ
      = ∑ a : NonzeroMask n, (v a * (∑ s, gibbsWeight ℓ s * chi a.1 s)) / Zpart ℓ := by
    rw [← numX]; simp only [Finset.sum_div]
  unfold xcoord
  rw [Xdist]
  refine Finset.sum_congr rfl (fun a _ => by rw [mul_div_assoc])

/-- Paper XII, Section 8.1 (the rank-one subtraction, quadratic-form identity).
`vᵀ 𝔼[χχᵀ] v - vᵀ Cov v = (∑_a v_a x_a)²`. -/
lemma quadForm_covMatrix_eq (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (secondMomentMatrix ℓ) v - quadForm (covMatrix ℓ) v
      = (∑ a : NonzeroMask n, v a * xcoord ℓ a) ^ 2 := by
  unfold quadForm secondMomentMatrix covMatrix
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => by ring)

/-- Paper XII, Section 8.1.  The quadratic form of `𝔼[χχᵀ]` in closed form:
`vᵀ 𝔼[χχᵀ] v = (∑_s w_ℓ(s)(∑_a v_a χ_a(s))²)/Z(ℓ)`. -/
lemma quadForm_secondMomentMatrix (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (secondMomentMatrix ℓ) v
      = (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2) / Zpart ℓ := by
  have e1 : ∀ s : Point n,
      gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2
        = ∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
            v a * (gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b := by
    intro s
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  have numkey : (∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
        v a * (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b)
      = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2 := by
    have L : (∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
          v a * (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b)
        = ∑ a : NonzeroMask n, ∑ b : NonzeroMask n, ∑ s,
            v a * (gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [L, Finset.sum_congr rfl (fun s _ => e1 s)]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  have Rdist : (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2) / Zpart ℓ
      = ∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
          (v a * (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b) / Zpart ℓ := by
    rw [← numkey]
    simp only [Finset.sum_div]
  rw [Rdist]
  unfold quadForm secondMomentMatrix secondMoment
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-- Paper XII, Section 8.1.  `𝔼[χχᵀ] ⪰ 0` (a nonnegative mixture of rank-one
outer products `χ(s)χ(s)ᵀ`). -/
theorem secondMomentMatrix_psd (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    0 ≤ quadForm (secondMomentMatrix ℓ) v := by
  rw [quadForm_secondMomentMatrix]
  refine div_nonneg (Finset.sum_nonneg (fun s _ => ?_)) (Zpart_pos ℓ).le
  exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- Paper XII, Section 3.  `∇²F = Cov_{P_ℓ}(χ) ⪰ 0` (a covariance matrix):
`vᵀ Cov v = Var_{P_ℓ}(∑_a v_a χ_a) ≥ 0`, by Cauchy–Schwarz. -/
theorem covMatrix_psd (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    0 ≤ quadForm (covMatrix ℓ) v := by
  have hZ := Zpart_pos ℓ
  have hsq : ∀ s, (0:ℝ) ≤ gibbsWeight ℓ s := fun s => (Real.exp_pos _).le
  have hCS : (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s)) ^ 2
      ≤ Zpart ℓ * (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2) := by
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun s => Real.sqrt (gibbsWeight ℓ s))
      (fun s => Real.sqrt (gibbsWeight ℓ s) * (∑ a : NonzeroMask n, v a * chi a.1 s))
    have e_fg : (∑ s, Real.sqrt (gibbsWeight ℓ s)
          * (Real.sqrt (gibbsWeight ℓ s) * (∑ a : NonzeroMask n, v a * chi a.1 s)))
        = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) :=
      Finset.sum_congr rfl (fun s _ => by rw [← mul_assoc, Real.mul_self_sqrt (hsq s)])
    have e_f2 : (∑ s, Real.sqrt (gibbsWeight ℓ s) ^ 2) = Zpart ℓ := by
      unfold Zpart
      exact Finset.sum_congr rfl (fun s _ => Real.sq_sqrt (hsq s))
    have e_g2 : (∑ s, (Real.sqrt (gibbsWeight ℓ s)
          * (∑ a : NonzeroMask n, v a * chi a.1 s)) ^ 2)
        = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2 :=
      Finset.sum_congr rfl (fun s _ => by rw [mul_pow, Real.sq_sqrt (hsq s)])
    rw [e_fg, e_f2, e_g2] at cs
    exact cs
  have goal2 : (∑ a : NonzeroMask n, v a * xcoord ℓ a) ^ 2
      ≤ quadForm (secondMomentMatrix ℓ) v := by
    rw [quadForm_secondMomentMatrix, sum_v_xcoord, div_pow,
        div_le_div_iff₀ (pow_pos hZ 2) hZ]
    nlinarith [mul_le_mul_of_nonneg_right hCS hZ.le]
  linarith [quadForm_covMatrix_eq ℓ v, goal2]

/-- `𝔼[χχᵀ]` is symmetric (`χ_a χ_b = χ_b χ_a`). -/
theorem secondMomentMatrix_isSymm (ℓ : NonzeroMask n → ℝ) :
    (secondMomentMatrix ℓ).IsSymm := by
  unfold Matrix.IsSymm
  ext a b
  simp only [Matrix.transpose_apply, secondMomentMatrix, secondMoment]
  congr 1
  exact Finset.sum_congr rfl (fun s _ => by ring)

/-- Paper XII, Section 8.1 (the rank-one subtraction).  `Cov ⪯ 𝔼[χχᵀ]` in the
PSD order: `vᵀ Cov v = vᵀ𝔼[χχᵀ]v - (∑_a v_a x_a)² ≤ vᵀ𝔼[χχᵀ]v`. -/
theorem covMatrix_le_secondMoment (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (covMatrix ℓ) v ≤ quadForm (secondMomentMatrix ℓ) v := by
  have hsplit : quadForm (secondMomentMatrix ℓ) v - quadForm (covMatrix ℓ) v
      = (∑ a : NonzeroMask n, v a * xcoord ℓ a) ^ 2 := by
    unfold quadForm secondMomentMatrix covMatrix
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  nlinarith [sq_nonneg (∑ a : NonzeroMask n, v a * xcoord ℓ a), hsplit]

/-- **The operator-norm-≤-trace step of Lemma 8.2** (stated generally).  For a
symmetric positive-semidefinite matrix `H`, `⟨v, Hv⟩ ≤ (tr H) ‖v‖₂²`; i.e. the
operator norm of a PSD matrix is at most its trace.

Left as `sorry`: this is the spectral-theorem step (op-norm `= λ_max ≤ ∑ λ_i
= tr H`) and is *not* a short proof in Lean — it needs the Hermitian spectral
decomposition (`Matrix.IsHermitian.spectral_theorem` and eigenvalue
nonnegativity).  Cf. Lemma 8.2. -/
theorem opNorm_le_trace_of_psd
    (H : Matrix (NonzeroMask n) (NonzeroMask n) ℝ)
    (_hsymm : H.IsSymm)
    (_hpsd : ∀ v, 0 ≤ quadForm H v)
    (v : NonzeroMask n → ℝ) :
    quadForm H v ≤ Matrix.trace H * ∑ a, (v a) ^ 2 := by
  sorry
  -- Spectral theorem for symmetric PSD `H`: `⟨v,Hv⟩ ≤ λ_max ‖v‖² ≤ (tr H)‖v‖²`
  -- because `λ_max ≤ ∑ λ_i = tr H` and all `λ_i ≥ 0`.  NOT native_decide; NOT
  -- short in Lean.  Cf. Lemma 8.2.

/-! ## Lemma 8.1 — the a posteriori error radius -/

/-- Paper XII, Lemma 8.1 (a posteriori radius).  Fix an orientation `ε` and any
`ℓ̃ ∈ ℝ^{N-1}`.  Let `ρ = ‖∇G_ε(ℓ̃)‖₂` and let `λ = min_a e^{-ε_a ℓ̃_a}` (encoded
as `IsLeast` of the range of the barrier weights).  If `r₀ := 2eρ/λ ≤ 1`, then
the true minimizer satisfies `‖ℓ⋆ - ℓ̃‖₂ ≤ r₀`. -/
theorem lemma_8_1
    (ε : Orientation n) (ℓt : NonzeroMask n → ℝ)
    (ρ lam r₀ : ℝ)
    (hρ : ρ = l2norm (gradG ε ℓt))
    (hlam : IsLeast (Set.range fun a => Real.exp (- ε.sign a * ℓt a)) lam)
    (hr₀ : r₀ = 2 * Real.exp 1 * ρ / lam)
    (hle : r₀ ≤ 1) :
    l2norm (lstar ε - ℓt) ≤ r₀ := by
  sorry
  -- If `ρ = 0` then `ℓ̃` is critical, so `ℓ̃ = ℓ⋆` by strict convexity.  Else set
  -- `T = ‖ℓ⋆ - ℓ̃‖₂`, `v = (ℓ⋆ - ℓ̃)/T`; `g(t) = ⟨∇G_ε(ℓ̃ + tv), v⟩` is
  -- nondecreasing (convexity) with `g(T) = 0`, `g(0) ≥ -ρ` (Cauchy–Schwarz).
  -- On `[0, r₀]` each coordinate moves ≤ 1, so barriers `≥ λ e⁻¹`, hence
  -- `∇²G_ε ⪰ λ e⁻¹ I` and `g(r₀) ≥ -ρ + r₀·λ/e = ρ > 0`, contradicting `g`
  -- nondecreasing with `g(T) = 0` at `T > r₀`.  Cf. Lemma 8.1.

/-! ## Lemma 8.2 — the entropy-transfer bound -/

/-- Paper XII, Section 8.  Coordinate (directional) partial derivative of a
function `f : ℝ^{N-1} → ℝ` in the `a`-th coordinate direction. -/
noncomputable def partialAt (f : (NonzeroMask n → ℝ) → ℝ)
    (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) : ℝ :=
  deriv (fun t : ℝ => f (ℓ + t • Pi.single a (1 : ℝ))) 0

/-- Paper XII, Lemma 8.2 (gradient identity).  `∇𝒟(ℓ) = ∇²F(ℓ) ℓ`, componentwise:
the `a`-th partial derivative of `𝒟` equals `(∇²F(ℓ) · ℓ)_a`. -/
theorem lemma_8_2_grad (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) :
    partialAt Dcal ℓ a = Matrix.mulVec (covMatrix ℓ) ℓ a := by
  sorry
  -- `log X_ℓ = ∑_a ℓ_a χ_a - F(ℓ)` gives `𝒟(ℓ) = ⟨ℓ, x(ℓ)⟩ - F(ℓ)` and
  -- `∇𝒟 = x + ∇²F ℓ - x = ∇²F ℓ = Cov_{P_ℓ}(χ) ℓ`.  Cf. Lemma 8.2.

/-- Paper XII, Lemma 8.2 (operator-norm bound).  `‖∇²F(ℓ)‖_op ≤ N - 1`, expressed
via the quadratic form: `vᵀ ∇²F(ℓ) v ≤ (N-1) ‖v‖₂²`.

Proof structure: `Cov ⪯ 𝔼[χχᵀ]` (rank-one subtraction), then op-norm `≤` trace
for the PSD `𝔼[χχᵀ]`, whose trace is `∑_{a≠0} 𝔼[χ_a²] = N - 1`.  Only the middle
(spectral) step is `sorry`. -/
theorem lemma_8_2_opNorm (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (covMatrix ℓ) v ≤ ((N n : ℝ) - 1) * ∑ a, (v a) ^ 2 := by
  calc quadForm (covMatrix ℓ) v
      ≤ quadForm (secondMomentMatrix ℓ) v := covMatrix_le_secondMoment ℓ v
    _ ≤ Matrix.trace (secondMomentMatrix ℓ) * ∑ a, (v a) ^ 2 :=
          opNorm_le_trace_of_psd _ (secondMomentMatrix_isSymm ℓ)
            (secondMomentMatrix_psd ℓ) v
    _ = ((N n : ℝ) - 1) * ∑ a, (v a) ^ 2 := by
          rw [trace_secondMomentMatrix_eq]

/-- Paper XII, Lemma 8.2 (entropy transfer).  In the setting of Lemma 8.1
(same `ε`, `ℓ̃ = ℓt`, `ρ`, `λ`, `r₀`), the entropy values at the numeric point
and the true minimizer differ by at most
`(N-1)(‖ℓ̃‖₂ + r₀) r₀`. -/
theorem lemma_8_2_transfer
    (ε : Orientation n) (ℓt : NonzeroMask n → ℝ)
    (ρ lam r₀ : ℝ)
    (hρ : ρ = l2norm (gradG ε ℓt))
    (hlam : IsLeast (Set.range fun a => Real.exp (- ε.sign a * ℓt a)) lam)
    (hr₀ : r₀ = 2 * Real.exp 1 * ρ / lam)
    (hle : r₀ ≤ 1) :
    |Dcal (lstar ε) - Dcal ℓt| ≤ ((N n : ℝ) - 1) * (l2norm ℓt + r₀) * r₀ := by
  sorry
  -- Mean-value inequality for `𝒟` along the segment `[ℓt, ℓ⋆]`: by Lemma 8.1
  -- the segment has length `≤ r₀` and its points have norm `≤ ‖ℓt‖₂ + r₀`;
  -- `∇𝒟 = ∇²F ℓ` (`lemma_8_2_grad`) and `‖∇²F‖_op ≤ N-1` (`lemma_8_2_opNorm`)
  -- give `‖∇𝒟(ℓ)‖ ≤ (N-1)(‖ℓt‖₂ + r₀)`.  Cf. Lemma 8.2.

/-! ## Theorem 8.3 — the finite main theorem (`2 ≤ n ≤ 5`) -/

/-- Paper XII, Theorem 8.3.  For `2 ≤ n ≤ 5`, every orientation satisfies
`m̂(ε) ≥ D_δ`, with equality iff `ε` is one of the `N` delta orientations
(certified margin at least `0.138`).

`sorry` — discharged by certified computation — exhaustive over the `2^{N-1}`
orientations for `n ≤ 4` and via the provably-complete 176-orbit `Γ_5`-transversal
for `n = 5` (Section 8.3), each orientation's entropy gap enclosed by exact
rational interval arithmetic through Lemmas 8.1–8.2; to be formalized with exact
`ℚ`/interval arithmetic, NOT native_decide. -/
theorem theorem_8_3 (hn : 2 ≤ n ∧ n ≤ 5) (ε : Orientation n) :
    Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε) := by
  sorry
  -- discharged by certified computation — exhaustive over the 2^{N-1}
  -- orientations for n≤4 and via the provably-complete 176-orbit Γ_5-transversal
  -- for n=5 (Section 8.3), each orientation's entropy gap enclosed by exact
  -- rational interval arithmetic through Lemmas 8.1–8.2; to be formalized with
  -- exact ℚ/interval arithmetic, NOT native_decide.

/-! ## Section 8.3 — the symmetry group `Γ_n` and the orbit-reduction interface -/

/-- Certified-local translation action on orientations (Certified's own orbit
model; named `cTrans` to avoid clashing with `Symmetry.transOrient`). -/
def cTrans (t : Point n) (ε : Orientation n) : Orientation n where
  sign := fun a => ε.sign a * chi a.1 t
  is_sign := fun a => by
    rcases ε.is_sign a with h | h <;> rcases chi_mem a.1 t with g | g <;> simp [h, g]

/-- Certified-local `GL(n,2)` action on orientations via a linear equivalence of
masks (`cGl φ ε` reindexes the signs by `φ⁻¹`); named `cGl` to avoid clashing
with `Symmetry.glOrient`.  The nonzero-preservation of `φ.symm` is left `sorry`. -/
noncomputable def cGl (φ : Point n ≃ₗ[ZMod 2] Point n) (ε : Orientation n) :
    Orientation n where
  sign := fun a => ε.sign ⟨φ.symm a.1, by sorry⟩
  is_sign := fun a => ε.is_sign _
/-- Paper XII, Lemma 3.3.  A `GL(n,2)` element is an `𝔽₂`-linear automorphism of
the mask space; it relabels a nonzero mask to another nonzero mask.  (`φ`
represents `M⁻ᵀ` in the paper's notation; as `M` ranges over `GL(n,2)`, so does
`φ` over all automorphisms of `𝔽₂ⁿ`.) -/
def maskMap (φ : Point n ≃ₗ[ZMod 2] Point n) (a : NonzeroMask n) : NonzeroMask n :=
  ⟨φ a.1, by
    intro h
    exact a.2 ((LinearEquiv.map_eq_zero_iff φ).1 h)⟩
    -- TODO(api): `LinearEquiv.map_eq_zero_iff : φ x = 0 ↔ x = 0`.

/-- Paper XII, Section 8.3.  One `Γ_n`-generator step: `ε'` is obtained from `ε`
by a translation or a `GL(n,2)` relabeling. -/
def gammaStep (ε ε' : Orientation n) : Prop :=
  (∃ t : Point n, ε' = cTrans t ε) ∨
  (∃ φ : Point n ≃ₗ[ZMod 2] Point n, ε' = cGl φ ε)

/-- Paper XII, Section 8.3.  `ε` and `ε'` lie in the same `Γ_n`-orbit iff they are
connected by generator steps (the equivalence closure of `gammaStep`). -/
def SameOrbit (ε ε' : Orientation n) : Prop := Relation.EqvGen gammaStep ε ε'
  -- TODO(api): `EqvGen r` is the equivalence-relation closure of `r`.

/-- Paper XII, Lemma 3.2 (Symmetry).  `m̂` is invariant under translations. -/
theorem mhat_transOrient (t : Point n) (ε : Orientation n) :
    mhat (cTrans t ε) = mhat ε := by
  sorry
  -- `ℓ' _a = ℓ_a χ_a(t)` is a linear bijection with `G_{τ_t ε}(ℓ') = G_ε(ℓ)`;
  -- the laws are translates and relative entropy to `U` is translation-invariant.
  -- Cf. Lemma 3.2.

/-- Paper XII, Lemma 3.3 (Symmetry).  `m̂` is invariant under `GL(n,2)`. -/
theorem mhat_glOrient (φ : Point n ≃ₗ[ZMod 2] Point n) (ε : Orientation n) :
    mhat (cGl φ ε) = mhat ε := by
  sorry
  -- `s ↦ M⁻¹ s` is a `U`-preserving bijection carrying `P_ε` to `P_{M·ε}`;
  -- relative entropy to `U` is invariant under `U`-preserving bijections.
  -- Cf. Lemma 3.3.

/-- Paper XII, Lemmas 3.2–3.3 (Symmetry).  `m̂` is constant on `Γ_n`-orbits. -/
theorem mhat_of_sameOrbit {ε ε' : Orientation n} (h : SameOrbit ε ε') :
    mhat ε = mhat ε' := by
  sorry
  -- `EqvGen` induction: reflexivity/symmetry/transitivity are immediate and each
  -- generator step is `mhat_transOrient` / `mhat_glOrient`.  Cf. Lemmas 3.2–3.3.

/-- Paper XII, Lemmas 3.2–3.3.  The delta family is a single `Γ_n`-orbit, so
`IsDelta` is `Γ_n`-invariant. -/
theorem isDelta_of_sameOrbit {ε ε' : Orientation n} (h : SameOrbit ε ε') :
    IsDelta ε ↔ IsDelta ε' := by
  sorry
  -- Translations act transitively on the `N` delta orientations and `GL(n,2)`
  -- maps the family to itself (`M·(delta at s⋆) = delta at M⁻¹ s⋆`).  Cf.
  -- Lemmas 3.2–3.3.

/-- Paper XII, Section 8.3.  The `Γ_n`-orbit of a representative `r`. -/
def orbitOf (r : Orientation n) : Set (Orientation n) := {ε | SameOrbit r ε}

/-- Paper XII, Section 8.3.  A **complete transversal** for the `Γ_n`-action on
orientations: a finite set of orbit representatives whose orbits cover every
orientation, together with the checksum that the orbit sizes sum to the total
number of orientations `2^{N-1}` (for `n = 5`, `2^{31}`).  The checksum is the
"provably complete by construction" certificate of Section 8.3 (cross-checked
against the Burnside count, receipt `w5`). -/
structure CompleteTransversal (reps : Finset (Orientation n)) : Prop where
  /-- Every orientation lies in the orbit of some representative. -/
  covers : ∀ ε : Orientation n, ∃ r ∈ reps, SameOrbit r ε
  /-- Orbit sizes sum to `2^{N-1}` (the `∑ orbit sizes = 2^{31}` checksum at
  `n = 5`). -/
  checksum : ∑ r ∈ reps, Nat.card (orbitOf r) = 2 ^ (N n - 1)

/-- Paper XII, Section 8.3 (orbit-reduction interface).  If `reps` is a complete
transversal and Theorem 8.3's two conclusions hold on every representative, then
they hold for **every** orientation.  This is exactly how `m̂` being
`Γ_n`-invariant (Symmetry) reduces the check to the representatives — for `n = 5`,
to the 176 orbits. -/
theorem reduce_to_transversal
    (reps : Finset (Orientation n)) (hCT : CompleteTransversal reps)
    (hreps : ∀ r ∈ reps, Ddelta n ≤ mhat r ∧ (mhat r = Ddelta n ↔ IsDelta r)) :
    ∀ ε : Orientation n, Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε) := by
  intro ε
  obtain ⟨r, hr, horb⟩ := hCT.covers ε
  have hm : mhat r = mhat ε := mhat_of_sameOrbit horb
  have hd : IsDelta r ↔ IsDelta ε := isDelta_of_sameOrbit horb
  obtain ⟨hge, hiff⟩ := hreps r hr
  refine ⟨hm ▸ hge, ?_⟩
  calc mhat ε = Ddelta n ↔ mhat r = Ddelta n := by rw [hm]
    _ ↔ IsDelta r := hiff
    _ ↔ IsDelta ε := hd

/-- Paper XII, Section 8.3.  The number of `Γ_n`-orbits of orientations. -/
noncomputable def orbitCount (n : ℕ) : ℕ :=
  Nat.card (Quot (gammaStep : Orientation n → Orientation n → Prop))

/-- Paper XII, Section 8.3.  The BFS over `{±1}^{31}` (with the `∑ orbit sizes =
2^{31}` checksum and the independent Burnside cross-check, receipt `w5`) yields
**176 orbits** at `n = 5`. -/
theorem orbitCount_five : orbitCount 5 = 176 := by
  sorry
  -- Certified: BFS over the 2^{31} states partitions them into 176 orbits; the
  -- orbit sizes sum to 2^{31} exactly, and an independent Burnside computation
  -- (averaging 2^{c(M)+n-r(M)} over GL(5,2)) reproduces 176.  Cf. Section 8.3.

/-- Paper XII, Section 8.2/8.3.  Cross-check: the same BFS/Burnside count gives
`2, 4, 14` orbits at `n = 2, 3, 4`, matching the exhaustive enumerations. -/
theorem orbitCount_low : orbitCount 2 = 2 ∧ orbitCount 3 = 4 ∧ orbitCount 4 = 14 := by
  sorry
  -- Cross-check of Section 8.2 exhaustive scans (8, 128, 32768 orientations) with
  -- the orbit BFS.  Cf. Section 8.3.

/-- Paper XII, Section 8.3.  Total number of orientations `= 2^{N-1}` (each is a
free `±1` choice per nonzero mask); underlies the `2^{31}` checksum at `n = 5`. -/
theorem nat_card_orientation (n : ℕ) : Nat.card (Orientation n) = 2 ^ (N n - 1) := by
  sorry
  -- Bijection `Orientation n ≃ (NonzeroMask n → Bool)` (a ±1 sign per nonzero
  -- mask), and `|NonzeroMask n| = N - 1` (`card_nonzeroMask`).  Cf. Section 8.3.

/-- Paper XII, Theorem 8.3 for `n = 5`, via the 176-orbit transversal.  Given the
provably-complete 176-representative `Γ_5`-transversal (with the `2^{31}`
checksum) and the per-representative certification of Lemmas 8.1–8.2, the main
inequality and equality set follow for **every** orientation on the `n = 5`
cube. -/
theorem theorem_8_3_n5_via_176_orbits
    (reps : Finset (Orientation 5)) (hCT : CompleteTransversal reps)
    (hcard : reps.card = 176)
    (hreps : ∀ r ∈ reps, Ddelta 5 ≤ mhat r ∧ (mhat r = Ddelta 5 ↔ IsDelta r)) :
    ∀ ε : Orientation 5, Ddelta 5 ≤ mhat ε ∧ (mhat ε = Ddelta 5 ↔ IsDelta ε) :=
  reduce_to_transversal reps hCT hreps

end WalshDelta
