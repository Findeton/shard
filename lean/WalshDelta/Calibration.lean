import Mathlib
import WalshDelta.Basic

/-!
# Walsh–delta: existence, uniqueness and the entropy gap (Paper XII, Section 3)

Formalization of Section 3 of

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube"  (Paper XII).

For a parameter vector `ℓ ∈ ℝ^{N-1}` (indexed by the nonzero Walsh masks) this
file introduces:

* the log-partition function
  `F(ℓ) = log 𝔼_U exp(∑_{a≠0} ℓ_a χ_a)`  (`logPartition`);
* the associated Gibbs law `P_ℓ ∝ exp(∑_{a≠0} ℓ_a χ_a)`  (`gibbs`), a
  `ProbLaw`;
* the character means `x_a(ℓ) = 𝔼_{P_ℓ}[χ_a] = ∂F/∂ℓ_a`  (`xa`);
* the calibration objective
  `G_ε(ℓ) = F(ℓ) + ∑_{a≠0} e^{-ε_a ℓ_a}`  (`Gfun`);
* the entropy gap of interest `m̂(ε) = D(P_ε ‖ U)`  (`mhat`).

The headline is **Theorem 3.1** (`theorem_3_1`): `G_ε` is smooth, strictly
convex and coercive; its unique minimizer `ℓ⋆` is the calibrated law of `ε`
with `h_a = ε_a ℓ⋆_a > 0`, and conversely every calibrated law arises this way,
so each orientation has exactly one calibrated law `P_ε`.

The section is decomposed into a convexity lemma (`Gfun_strictConvexOn`), a
coercivity lemma (`Gfun_coercive`), a critical-point = calibration lemma
(`critical_iff_calibrationEqs`, `calibrated_of_critical`, `hcoeff_pos_of_critical`)
and an existence/uniqueness statement (`Gfun_min_exists_unique`,
`calibrated_exists_unique`).
-/

namespace WalshDelta

open scoped BigOperators

variable {n : ℕ}

/-! ## The unsigned tilt, log-partition and Gibbs law -/

/-- Paper XII, Section 3.  The (unsigned) linear tilt attached to a parameter
vector `ℓ ∈ ℝ^{N-1}`: `L_ℓ(s) = ∑_{a≠0} ℓ_a χ_a(s)`.  Unlike `tilt` (which
carries the orientation signs), here the reals `ℓ_a` absorb the signs, so that
`ℓ_a = h_a ε_a` recovers `tilt ε h`. -/
def linForm (ℓ : NonzeroMask n → ℝ) (s : Point n) : ℝ :=
  ∑ a : NonzeroMask n, ℓ a * chi a.1 s

/-- Paper XII, Section 3.  The unnormalized partition sum
`Z(ℓ) = ∑_{r} exp(L_ℓ(r))`. -/
noncomputable def gibbsZ (ℓ : NonzeroMask n → ℝ) : ℝ :=
  ∑ r, Real.exp (linForm ℓ r)

/-- The partition sum is strictly positive (sum of exponentials over the
nonempty cube). -/
lemma gibbsZ_pos (ℓ : NonzeroMask n → ℝ) : 0 < gibbsZ ℓ := by
  apply Finset.sum_pos
  · intro r _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Paper XII, Section 3.  The log-partition function
`F(ℓ) = log 𝔼_U exp(∑_{a≠0} ℓ_a χ_a)`.  Its gradient is the character-mean
vector and its Hessian is `Cov_{P_ℓ}(χ) ⪰ 0` (used in `logPartition_convexOn`). -/
noncomputable def logPartition (ℓ : NonzeroMask n → ℝ) : ℝ :=
  Real.log (EU (fun s => Real.exp (linForm ℓ s)))

/-- Paper XII, Section 3.  The Gibbs law `P_ℓ(s) ∝ exp(∑_{a≠0} ℓ_a χ_a(s))`,
packaged as a full-support `ProbLaw`. -/
noncomputable def gibbs (ℓ : NonzeroMask n → ℝ) : ProbLaw n where
  P := fun s => Real.exp (linForm ℓ s) / gibbsZ ℓ
  pos := fun s => div_pos (Real.exp_pos _) (gibbsZ_pos ℓ)
  sum_one := by
    have hZ : gibbsZ ℓ ≠ 0 := (gibbsZ_pos ℓ).ne'
    rw [← Finset.sum_div]
    show gibbsZ ℓ / gibbsZ ℓ = 1
    exact div_self hZ

/-- Paper XII, Section 3.  The character means of the Gibbs law,
`x_a(ℓ) = 𝔼_{P_ℓ}[χ_a]`.  Theorem 3.1's gradient identity reads
`∂F/∂ℓ_a = x_a(ℓ)`. -/
noncomputable def xa (ℓ : NonzeroMask n → ℝ) (a : Point n) : ℝ :=
  EP (gibbs ℓ) (fun s => chi a s)

/-! ## The calibration objective `G_ε` -/

/-- Paper XII, Theorem 3.1.  The calibration objective
`G_ε(ℓ) = F(ℓ) + ∑_{a≠0} e^{-ε_a ℓ_a}`. -/
noncomputable def Gfun (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) : ℝ :=
  logPartition ℓ + ∑ a : NonzeroMask n, Real.exp (-(ε.sign a * ℓ a))

/-! ## Coercivity predicate -/

/-- Coercivity on the finite-dimensional space `ℝ^{N-1}`: `g(ℓ) → ∞` as
`‖ℓ‖ → ∞`.  (Equivalently `Tendsto g (cocompact _) atTop`.) -/
def Coercive (g : (NonzeroMask n → ℝ) → ℝ) : Prop :=
  ∀ C : ℝ, ∃ R : ℝ, ∀ ℓ : NonzeroMask n → ℝ, R ≤ ‖ℓ‖ → C ≤ g ℓ

/-! ## Smoothness -/

/-- Paper XII, Theorem 3.1 (smoothness).  `F` is smooth: `𝔼_U exp(L_ℓ) > 0` for
every `ℓ`, and `log` of a strictly positive smooth function is smooth. -/
lemma logPartition_contDiff : ContDiff ℝ ⊤ (logPartition (n := n)) := by
  sorry
  -- `L_ℓ` is linear (hence smooth) in `ℓ`; `s ↦ exp(L_ℓ(s))` and its uniform
  -- average are smooth and strictly positive; `Real.log` is smooth on `(0,∞)`.
  -- Cf. Theorem 3.1, "Smoothness and strict convexity".
  -- TODO(api): '⊤' denotes C^ω in current Mathlib; the statement is true at
  -- that strength since `exp`/`log∘(>0)` are analytic. Weaken to `∞` for C^∞.

/-- Paper XII, Theorem 3.1 (smoothness).  Each barrier `ℓ ↦ e^{-ε_a ℓ_a}` and
hence the whole objective `G_ε` is smooth. -/
lemma Gfun_contDiff (ε : Orientation n) : ContDiff ℝ ⊤ (Gfun ε) := by
  sorry
  -- `Gfun ε = logPartition + ∑_a exp(-ε_a·(·)_a)`; a finite sum of smooth
  -- functions is smooth. Cf. Theorem 3.1.
  -- TODO(api): as in `logPartition_contDiff`, '⊤' = C^ω here.

/-! ## Convexity lemma -/

/-- Paper XII, Theorem 3.1 (convexity of `F`).  `∇²F = Cov_{P_ℓ}(χ) ⪰ 0`, so
`F` is convex on `ℝ^{N-1}`. -/
lemma logPartition_convexOn :
    ConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ)) (logPartition (n := n)) := by
  sorry
  -- The Hessian of a log-partition function is the covariance matrix
  -- `Cov_{P_ℓ}(χ) ⪰ 0`; a `C²` function with PSD Hessian is convex.
  -- Cf. Theorem 3.1, "Smoothness and strict convexity".

/-- Paper XII, Theorem 3.1 (strict convexity).  Each barrier
`e^{-ε_a ℓ_a}` is smooth and convex with strictly positive second derivative in
the coordinate `ℓ_a`, so `∇²G_ε ⪰ diag(e^{-ε_a ℓ_a}) ≻ 0` and `G_ε` is
strictly convex. -/
lemma Gfun_strictConvexOn (ε : Orientation n) :
    StrictConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ)) (Gfun ε) := by
  sorry
  -- `F` convex (`logPartition_convexOn`) plus the strictly convex separable
  -- barrier `∑_a e^{-ε_a ℓ_a}` (second derivative `e^{-ε_a ℓ_a} > 0` in each
  -- coordinate) give `∇²G_ε ≻ 0`. Cf. Theorem 3.1.

/-! ## Coercivity lemma -/

/-- Paper XII, Theorem 3.1 (coercivity, radial step).  For every unit direction
`v ≠ 0`, `μ(v) := max_s ⟨v, χ(s)⟩ > 0` (the characters are linearly independent
and `⟨v, χ(·)⟩` has zero mean), whence `F(tv) ≥ t μ(v) − log N → ∞`. -/
lemma logPartition_radial_tendsto (v : NonzeroMask n → ℝ) (hv : v ≠ 0) :
    Filter.Tendsto (fun t : ℝ => logPartition (fun a => t * v a)) Filter.atTop
      Filter.atTop := by
  sorry
  -- `s ↦ ∑_a v_a χ_a(s)` has zero `U`-mean and is not ≡ 0, so its max `μ(v)>0`;
  -- bounding `𝔼_U exp` below by its top term at an attaining `s` gives
  -- `F(tv) ≥ t μ(v) − log N`. Cf. Theorem 3.1, "Coercivity".

/-- Paper XII, Theorem 3.1 (coercivity).  `G_ε` is coercive on `ℝ^{N-1}`. -/
lemma Gfun_coercive (ε : Orientation n) : Coercive (Gfun ε) := by
  sorry
  -- The barrier terms are `≥ 0`, so `G_ε(tv) ≥ F(tv) → ∞` on every ray
  -- (`logPartition_radial_tendsto`); a finite convex (hence continuous) function
  -- that blows up on every ray blows up at infinity — the compactness/subsequence
  -- argument of Theorem 3.1, "Coercivity".

/-! ## Gradient and the critical-point = calibration lemma -/

/-- Paper XII, Section 3.  Partial derivative of the log-partition:
`∂F/∂ℓ_a = 𝔼_{P_ℓ}[χ_a] = x_a(ℓ)`. -/
lemma logPartition_partialDeriv (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) :
    deriv (fun t : ℝ => logPartition (Function.update ℓ a t)) (ℓ a)
      = xa ℓ a.1 := by
  sorry
  -- Differentiating `log 𝔼_U exp(∑_b ℓ_b χ_b)` in `ℓ_a` produces the Gibbs
  -- weighting: `∂F/∂ℓ_a = 𝔼_{P_ℓ}[χ_a] = x_a(ℓ)`. Cf. Section 3 (∂F/∂ℓ_a).

/-- Paper XII, Theorem 3.1 (critical equation).  Partial derivative of the
objective: `∂G_ε/∂ℓ_a = x_a(ℓ) − ε_a e^{-ε_a ℓ_a}`. -/
lemma Gfun_partialDeriv (ε : Orientation n) (ℓ : NonzeroMask n → ℝ)
    (a : NonzeroMask n) :
    deriv (fun t : ℝ => Gfun ε (Function.update ℓ a t)) (ℓ a)
      = xa ℓ a.1 - ε.sign a * Real.exp (-(ε.sign a * ℓ a)) := by
  sorry
  -- `∂/∂ℓ_a` of `F` is `x_a(ℓ)` (`logPartition_partialDeriv`); `∂/∂ℓ_a` of the
  -- barrier `e^{-ε_a ℓ_a}` is `-ε_a e^{-ε_a ℓ_a}`; all other barriers are
  -- independent of `ℓ_a`. Cf. Theorem 3.1, "The critical equations".

/-- Paper XII, Theorem 3.1.  `ℓ` is a critical point of `G_ε` when every partial
derivative vanishes. -/
def IsCritical (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) : Prop :=
  ∀ a : NonzeroMask n,
    deriv (fun t : ℝ => Gfun ε (Function.update ℓ a t)) (ℓ a) = 0

/-- Paper XII, Theorem 3.1 (critical point = calibration equations).  `ℓ` is a
critical point of `G_ε` iff the self-calibration fixed point holds for `P_ℓ`
with `h_a = ε_a ℓ_a`, i.e. `𝔼_{P_ℓ}[ε_a χ_a] = e^{-ε_a ℓ_a}` for every
`a ≠ 0`. -/
lemma critical_iff_calibrationEqs (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) :
    IsCritical ε ℓ ↔
      ∀ a : NonzeroMask n,
        EP (gibbs ℓ) (fun s => ε.sign a * chi a.1 s)
          = Real.exp (-(ε.sign a * ℓ a)) := by
  sorry
  -- `∂G_ε/∂ℓ_a = x_a(ℓ) − ε_a e^{-ε_a ℓ_a} = 0 ⟺ x_a(ℓ) = ε_a e^{-ε_a ℓ_a}
  -- ⟺ 𝔼_{P_ℓ}[ε_a χ_a] = ε_a x_a(ℓ) = e^{-ε_a ℓ_a}` (using `ε_a² = 1` and
  -- `EP` linearity). Cf. Theorem 3.1, "The critical equations are the
  -- calibration", together with `Gfun_partialDeriv`.

/-- Paper XII, Theorem 3.1 (critical point ⇒ calibrated law).  A critical point
`ℓ` yields a calibrated law `P_ℓ` for `ε` with parameters `h_a = ε_a ℓ_a`. -/
lemma calibrated_of_critical (ε : Orientation n) (ℓ : NonzeroMask n → ℝ)
    (hcrit : IsCritical ε ℓ) : Calibrated (gibbs ℓ) ε := by
  refine ⟨fun a => ε.sign a * ℓ a, ?_, ?_⟩
  · sorry
    -- Gibbs form: with `h_a = ε_a ℓ_a` one has `∑_a h_a ε_a χ_a = ∑_a ℓ_a χ_a
    -- = L_ℓ` (since `ε_a² = 1`), so `tilt ε h = linForm ℓ` and the normalized
    -- Gibbs density `P_ℓ` matches Definition 1.1's exponential form. Cf.
    -- Theorem 3.1.
  · intro a
    have := (critical_iff_calibrationEqs ε ℓ).1 hcrit a
    -- `𝔼_{P_ℓ}[ε_a χ_a] = e^{-ε_a ℓ_a} = e^{-h_a}` with `h_a = ε_a ℓ_a`.
    simpa using this

/-- Paper XII, Theorem 3.1 (positivity of the parameters).  At a critical point
`h_a = ε_a ℓ_a > 0` for every nonzero mask, because
`e^{-h_a} = |𝔼_P[χ_a]| < 1` for any full-support law with the nonconstant
`±1`-valued `χ_a`. -/
lemma hcoeff_pos_of_critical (ε : Orientation n) (ℓ : NonzeroMask n → ℝ)
    (hcrit : IsCritical ε ℓ) (a : NonzeroMask n) : 0 < ε.sign a * ℓ a := by
  sorry
  -- `e^{-ε_a ℓ_a} = |𝔼_{P_ℓ}[χ_a]| < 1` (full support, `χ_a` nonconstant of
  -- modulus 1), so `ε_a ℓ_a > 0`. Cf. Theorem 3.1 and Definition 1.1 (h_a > 0).

/-! ## Existence, uniqueness, and the calibrated law `P_ε` -/

/-- Paper XII, Theorem 3.1 (existence and uniqueness of the minimizer).  The
smooth, strictly convex, coercive `G_ε` attains a unique global minimum. -/
lemma Gfun_min_exists_unique (ε : Orientation n) :
    ∃! ℓstar : NonzeroMask n → ℝ,
      IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) ℓstar := by
  sorry
  -- Coercivity (`Gfun_coercive`) + continuity give existence of a global
  -- minimizer; strict convexity (`Gfun_strictConvexOn`) gives uniqueness.
  -- Cf. Theorem 3.1, "Coercivity".

/-- Paper XII, Theorem 3.1.  The unique minimizer `ℓ⋆(ε)` of `G_ε`. -/
noncomputable def ellStar (ε : Orientation n) : NonzeroMask n → ℝ :=
  Classical.choose (Gfun_min_exists_unique ε)

/-- `ℓ⋆(ε)` is indeed a global minimizer of `G_ε`. -/
lemma ellStar_isMinOn (ε : Orientation n) :
    IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) (ellStar ε) :=
  (Classical.choose_spec (Gfun_min_exists_unique ε)).1

/-- Paper XII, Theorem 3.1.  The (unique) calibrated law of `ε`,
`P_ε := P_{ℓ⋆(ε)}`. -/
noncomputable def calLaw (ε : Orientation n) : ProbLaw n :=
  gibbs (ellStar ε)

/-- Paper XII, Theorem 3.1.  The minimizer `ℓ⋆` is a critical point of `G_ε`. -/
lemma ellStar_isCritical (ε : Orientation n) : IsCritical ε (ellStar ε) := by
  sorry
  -- Interior global minimizer of a differentiable function on `ℝ^{N-1}` has
  -- vanishing gradient (Fermat). Cf. Theorem 3.1.

/-- Paper XII, Theorem 3.1.  The calibrated law `P_ε` is calibrated for `ε`. -/
lemma calLaw_calibrated (ε : Orientation n) : Calibrated (calLaw ε) ε :=
  calibrated_of_critical ε (ellStar ε) (ellStar_isCritical ε)

/-- Paper XII, Theorem 3.1 ("exactly one calibrated law").  Every orientation
has a unique calibrated law. -/
theorem calibrated_exists_unique (ε : Orientation n) :
    ∃! P : ProbLaw n, Calibrated P ε := by
  sorry
  -- Existence: `calLaw_calibrated`. Uniqueness: any calibrated `P` is a Gibbs
  -- law `P_ℓ` with `ℓ_a = h_a ε_a` satisfying the same first-order equations,
  -- i.e. a critical point of the strictly convex `G_ε`, hence equal to `ℓ⋆`;
  -- so `P = P_{ℓ⋆} = P_ε`. Cf. Theorem 3.1, "The critical equations are the
  -- calibration".

/-! ## The entropy gap of interest -/

/-- Paper XII, Section 1.1 / Section 3.  The entropy gap of the orientation,
`m̂(ε) = D(P_ε ‖ U) = 𝔼_U[X log X] ≥ 0` — the quantity minimized by the main
theorem. -/
noncomputable def mhat (ε : Orientation n) : ℝ := Dkl (calLaw ε)

/-- Paper XII, §1.2.  The delta entropy value `D_δ = m̂(ε⋆)` (canonical home). -/
noncomputable def Ddelta (n : ℕ) : ℝ := mhat (deltaOrientation (0 : Point n))

/-! ## Theorem 3.1 (headline) -/

/-- Paper XII, Theorem 3.1 (existence and uniqueness).  For every orientation
`ε`, the objective `G_ε` is smooth, strictly convex and coercive on
`ℝ^{N-1}`; its unique global minimizer `ℓ⋆` gives the calibrated law of `ε`
with `h_a = ε_a ℓ⋆_a > 0`, and conversely every calibrated law arises this
way.  In particular each orientation has exactly one calibrated law `P_ε`. -/
theorem theorem_3_1 (ε : Orientation n) :
    ContDiff ℝ ⊤ (Gfun ε)
    ∧ StrictConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ)) (Gfun ε)
    ∧ Coercive (Gfun ε)
    ∧ IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) (ellStar ε)
    ∧ Calibrated (calLaw ε) ε
    ∧ (∀ a : NonzeroMask n, 0 < ε.sign a * ellStar ε a)
    ∧ (∃! P : ProbLaw n, Calibrated P ε) := by
  refine ⟨Gfun_contDiff ε, Gfun_strictConvexOn ε, Gfun_coercive ε,
    ellStar_isMinOn ε, calLaw_calibrated ε, ?_, calibrated_exists_unique ε⟩
  intro a
  exact hcoeff_pos_of_critical ε (ellStar ε) (ellStar_isCritical ε) a

end WalshDelta
