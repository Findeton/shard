import Mathlib
import WalshDelta.Basic
import WalshDelta.Calibration

/-!
# Walsh–delta: the delta laws in closed form (Paper XII, Sections 1.2 and 4)

Formalization of the delta orientations `ε⋆` (Section 1.2), Proposition 4.1
(their calibrated law is an explicit two-level law governed by the root `u⋆`
of `p(u) = u^{N+1} + u^N + (N-1)u - 1`), the resulting gap
`D_δ = ŵm(ε⋆)`, and Lemma 4.2 (`0 < D_δ < 1/(N-1)` with `N·D_δ → 1`).

The delta orientation itself, `deltaOrientation sstar` with
`ε⋆_a = -χ_a(sstar)`, is defined in `WalshDelta.Basic`; we reuse it verbatim.

## Section 3 interface used here

`ŵm(ε) = D(P_ε ‖ U)` is the relative entropy of the *unique* calibrated law
`P_ε` of `ε` (Theorem 3.1).  The existence/uniqueness of `P_ε` (Theorem 3.1)
and translation covariance (Lemma 3.2) live in the Section-3 development; the
declarations `exists_unique_calibrated`, `calLaw`, `mhat`, `tauOrient`,
`mhat_tauOrient` below are exactly that interface, restated here as the part of
Section 3 that Section 4 consumes.  At assembly they are to be unified with the
Section-3 module (identical statements).
-/

namespace WalshDelta

open Classical

open scoped BigOperators
open Filter Topology

variable {n : ℕ}

/-- For `n ≥ 2`, `1 < N = 2ⁿ` as a real (in fact `4 ≤ N`). -/
lemma one_lt_N (n : ℕ) (hn : 2 ≤ n) : (1:ℝ) < (N n : ℝ) := by
  have h4 : (4:ℕ) ≤ N n := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : (4:ℝ) ≤ (N n : ℝ) := by exact_mod_cast h4
  linarith

/-! ## Walsh orthogonality / inversion helpers (Section 1.1, used in §4) -/

/-- Paper XII, Section 1.1: bilinearity of the pairing gives multiplicativity of
`χ_a` in its POINT argument, `χ_a(s+t) = χ_a(s)·χ_a(t)` (companion of
`chi_add`, which is multiplicativity in the mask). -/
lemma chi_right_add (a s t : Point n) : chi a (s + t) = chi a s * chi a t := by
  have hadd : dotZ2 a (s + t) = dotZ2 a s + dotZ2 a t := by
    simp only [dotZ2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hv : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have key : ∀ x y : ZMod 2, (if x + y = 0 then (1:ℝ) else -1)
      = (if x = 0 then (1:ℝ) else -1) * (if y = 0 then (1:ℝ) else -1) := by
    intro x y; rcases hv x with hx | hx <;> rcases hv y with hy | hy <;>
      subst hx <;> subst hy <;> simp [show (1:ZMod 2) + 1 = 0 from by decide]
  simp only [chi, hadd]; exact key _ _

/-- Paper XII, Section 1.1 (Walsh orthogonality), used in the Prop 4.1 proof:
`∑_s χ_a(s) = N·[a = 0]`. -/
lemma sum_chi (a : Point n) :
    (∑ s, chi a s) = if a = 0 then (N n : ℝ) else 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    simp only [chi_zero, Finset.sum_const, Finset.card_univ, card_point, nsmul_eq_mul, mul_one]
  · rw [if_neg ha]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    simp only [Pi.zero_apply] at hj
    set ej : Point n := Pi.single j (1 : ZMod 2) with hej
    have hdot : dotZ2 a ej = a j := by
      unfold dotZ2
      rw [Finset.sum_eq_single j]
      · rw [hej, Pi.single_eq_same, mul_one]
      · intro i _ hij; rw [hej, Pi.single_eq_of_ne hij, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hchi_ej : chi a ej = -1 := by unfold chi; rw [hdot, if_neg hj]
    have hbij : (∑ s, chi a (s + ej)) = ∑ s, chi a s :=
      Fintype.sum_equiv (Equiv.addRight ej) (fun s => chi a (s + ej)) (chi a) (fun x => rfl)
    have hflip : (∑ s, chi a (s + ej)) = ∑ s, (- chi a s) :=
      Finset.sum_congr rfl (fun s _ => by rw [chi_right_add, hchi_ej, mul_neg_one])
    rw [hflip, Finset.sum_neg_distrib] at hbij
    linarith [hbij]

/-- Paper XII, Section 4 (Walsh inversion, used in the closed form of `X`):
`∑_{a≠0} χ_a(s) = N·[s = 0] - 1`.  This is `sum_chi` read on the self-dual
group (masks and points share the type). -/
lemma sum_nonzero_chi (s : Point n) :
    (∑ a : NonzeroMask n, chi a.1 s) = (if s = 0 then (N n : ℝ) else 0) - 1 := by
  have hsub : (∑ a ∈ Finset.univ.erase (0 : Point n), chi a s)
      = ∑ a : NonzeroMask n, chi a.1 s :=
    Finset.sum_subtype _ (fun x => by simp [Finset.mem_erase]) (fun a => chi a s)
  have herase : (∑ a ∈ Finset.univ.erase (0 : Point n), chi a s)
      = (∑ a : Point n, chi a s) - chi 0 s :=
    Finset.sum_erase_eq_sub (Finset.mem_univ 0)
  have hsym : (∑ a : Point n, chi a s) = ∑ a : Point n, chi s a :=
    Finset.sum_congr rfl (fun a _ => by
      unfold chi dotZ2; rw [Finset.sum_congr rfl (fun i _ => mul_comm (a i) (s i))])
  rw [← hsub, herase, hsym, sum_chi s, chi_zero]

/-! ## The delta polynomial `p` and its positive root `u⋆` (Prop 4.1) -/

/-- Paper XII, Proposition 4.1.  The delta polynomial
`p(u) = u^{N+1} + u^N + (N-1)u - 1`, whose unique positive root controls the
delta law. -/
def deltaPoly (n : ℕ) (u : ℝ) : ℝ :=
  u ^ (N n + 1) + u ^ (N n) + ((N n : ℝ) - 1) * u - 1

/-- Paper XII, Proposition 4.1: `p(0) = -1 < 0`. -/
lemma deltaPoly_zero (n : ℕ) : deltaPoly n 0 = -1 := by
  have h1 : N n ≠ 0 := (N_pos n).ne'
  rw [deltaPoly, zero_pow (by omega : N n + 1 ≠ 0), zero_pow h1]
  ring

/-- Paper XII, Proposition 4.1: `p` is strictly increasing on `[0,∞)` (its
derivative `(N+1)u^N + N u^{N-1} + (N-1)` is positive there). -/
lemma deltaPoly_strictMonoOn (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (deltaPoly n) (Set.Ici (0 : ℝ)) := by
  have hN1 : (1:ℝ) < (N n : ℝ) := one_lt_N n hn
  intro x hx y _ hxy
  simp only [Set.mem_Ici] at hx
  unfold deltaPoly
  have h1 : x ^ (N n + 1) ≤ y ^ (N n + 1) := pow_le_pow_left₀ hx hxy.le _
  have h2 : x ^ (N n) ≤ y ^ (N n) := pow_le_pow_left₀ hx hxy.le _
  have h3 : ((N n : ℝ) - 1) * x < ((N n : ℝ) - 1) * y :=
    mul_lt_mul_of_pos_left hxy (by linarith)
  linarith

/-- Paper XII, Proposition 4.1: `p(1/(N-1)) > 0`. -/
lemma deltaPoly_pos_at_bound (n : ℕ) (hn : 2 ≤ n) :
    0 < deltaPoly n (1 / ((N n : ℝ) - 1)) := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  set c := 1 / ((N n : ℝ) - 1) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcancel : ((N n : ℝ) - 1) * c = 1 := by rw [hc, mul_one_div, div_self hN1.ne']
  have hval : deltaPoly n c = c ^ (N n + 1) + c ^ (N n) := by
    unfold deltaPoly; rw [hcancel]; ring
  rw [hval]
  exact add_pos (pow_pos hcpos _) (pow_pos hcpos _)

/-- Paper XII, Proposition 4.1: `p` has a unique positive root, and it lies in
`(0, 1/(N-1))`.  (Existence/uniqueness follow from `deltaPoly_zero`,
`deltaPoly_pos_at_bound`, and strict monotonicity on `[0,∞)`.) -/
theorem uStar_exists_unique (n : ℕ) (hn : 2 ≤ n) :
    ∃! u : ℝ, 0 < u ∧ deltaPoly n u = 0 := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  set c := 1 / ((N n : ℝ) - 1) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcont : Continuous (deltaPoly n) := by unfold deltaPoly; fun_prop
  have hp0 : deltaPoly n 0 = -1 := deltaPoly_zero n
  have hpc : 0 < deltaPoly n c := deltaPoly_pos_at_bound n hn
  have hmem : (0:ℝ) ∈ Set.Icc (deltaPoly n 0) (deltaPoly n c) := by
    rw [hp0]; exact ⟨by linarith, le_of_lt hpc⟩
  obtain ⟨u, hu_mem, hu_zero⟩ := intermediate_value_Icc hcpos.le hcont.continuousOn hmem
  have hupos : 0 < u := by
    rcases lt_or_eq_of_le hu_mem.1 with h | h
    · exact h
    · exfalso; rw [← h, hp0] at hu_zero; norm_num at hu_zero
  refine ⟨u, ⟨hupos, hu_zero⟩, ?_⟩
  rintro v ⟨hvpos, hvzero⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := deltaPoly_strictMonoOn n hn (Set.mem_Ici.mpr hvpos.le) (Set.mem_Ici.mpr hupos.le) h
    rw [hvzero, hu_zero] at hlt; exact absurd hlt (lt_irrefl 0)
  · have hlt := deltaPoly_strictMonoOn n hn (Set.mem_Ici.mpr hupos.le) (Set.mem_Ici.mpr hvpos.le) h
    rw [hvzero, hu_zero] at hlt; exact absurd hlt (lt_irrefl 0)

/-- Paper XII, Proposition 4.1.  The unique positive root `u⋆` of `p`
(a junk value `0` off the meaningful range `n ≥ 2`, so that `u⋆` is total). -/
noncomputable def uStar (n : ℕ) : ℝ :=
  if h : ∃ u : ℝ, 0 < u ∧ deltaPoly n u = 0 then h.choose else 0

/-- Paper XII, Proposition 4.1: `u⋆` is a positive root of `p` (for `n ≥ 2`). -/
lemma uStar_spec (n : ℕ) (hn : 2 ≤ n) :
    0 < uStar n ∧ deltaPoly n (uStar n) = 0 := by
  have hx : ∃ u : ℝ, 0 < u ∧ deltaPoly n u = 0 := (uStar_exists_unique n hn).exists
  rw [uStar, dif_pos hx]
  exact hx.choose_spec

/-- Paper XII, Proposition 4.1: `u⋆ > 0`. -/
lemma uStar_pos (n : ℕ) (hn : 2 ≤ n) : 0 < uStar n := (uStar_spec n hn).1

/-- Paper XII, Proposition 4.1: `p(u⋆) = 0`. -/
lemma deltaPoly_uStar (n : ℕ) (hn : 2 ≤ n) : deltaPoly n (uStar n) = 0 :=
  (uStar_spec n hn).2

/-- Paper XII, Proposition 4.1: `u⋆ ∈ (0, 1/(N-1))`. -/
lemma uStar_lt (n : ℕ) (hn : 2 ≤ n) : uStar n < 1 / ((N n : ℝ) - 1) := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hb : (0:ℝ) ≤ 1 / ((N n : ℝ) - 1) := le_of_lt (by positivity)
  by_contra hle
  push_neg at hle
  have hmono := (deltaPoly_strictMonoOn n hn).monotoneOn
    (Set.mem_Ici.mpr hb) (Set.mem_Ici.mpr (uStar_pos n hn).le) hle
  rw [deltaPoly_uStar n hn] at hmono
  linarith [deltaPoly_pos_at_bound n hn]

/-- Paper XII, Proposition 4.1: the calibration fixed point on the log-side,
`(1-(N-1)u)/(1+u) = u^N`, cleared of denominators, is exactly `p(u) = 0`. -/
lemma deltaPoly_root_iff (n : ℕ) (u : ℝ) :
    deltaPoly n u = 0 ↔ 1 - ((N n : ℝ) - 1) * u = u ^ (N n) * (1 + u) := by
  unfold deltaPoly
  rw [pow_succ, mul_add, mul_one]
  constructor <;> intro h <;> linarith

/-! ## The two-level delta law `X_δ` (Prop 4.1) -/

/-- Paper XII, Proposition 4.1.  The high level `A = 1 - (N-1)u⋆` (the value of
the density `X_δ` at the extinguished point `s⋆`). -/
noncomputable def deltaA (n : ℕ) : ℝ := 1 - ((N n : ℝ) - 1) * uStar n

/-- Paper XII, Proposition 4.1.  The bulk level `B = 1 + u⋆` (the value of the
density `X_δ` at every point `s ≠ s⋆`). -/
noncomputable def deltaB (n : ℕ) : ℝ := 1 + uStar n

/-- Paper XII, Proposition 4.1: `A = 1-(N-1)u⋆ > 0` (positivity of the Gibbs
law forces `u⋆ < 1/(N-1)`). -/
lemma deltaA_pos (n : ℕ) (hn : 2 ≤ n) : 0 < deltaA n := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hu := uStar_lt n hn
  have hlt : ((N n : ℝ) - 1) * uStar n < 1 := by
    have := (lt_div_iff₀ hN1).mp hu; nlinarith [this]
  unfold deltaA; linarith

/-- Paper XII, Proposition 4.1: `A = 1-(N-1)u⋆ < 1` (since `u⋆ > 0`). -/
lemma deltaA_lt_one (n : ℕ) (hn : 2 ≤ n) : deltaA n < 1 := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hu := uStar_pos n hn
  unfold deltaA; nlinarith [mul_pos hN1 hu]

/-- Paper XII, Proposition 4.1: `B = 1+u⋆ > 1`. -/
lemma deltaB_gt_one (n : ℕ) (hn : 2 ≤ n) : 1 < deltaB n := by
  have := uStar_pos n hn
  simp only [deltaB]; linarith

/-- Paper XII, Proposition 4.1 (two-level law).  The calibrated law of the
delta orientation at `s⋆`: the probability law with density
`X_δ(s⋆) = A = 1-(N-1)u⋆` and `X_δ(s) = B = 1+u⋆` for `s ≠ s⋆`, i.e.
`P(s) = X_δ(s)/N`. -/
noncomputable def deltaLaw (sstar : Point n) : ProbLaw n where
  P := fun s => (if s = sstar then deltaA n else deltaB n) / (N n : ℝ)
  pos := by
    sorry
    -- `A > 0` (deltaA_pos) and `B > 0` (deltaB_gt_one), divided by `N > 0`. Prop 4.1.
  sum_one := by
    sorry
    -- `A + (N-1)B = (1-(N-1)u⋆) + (N-1)(1+u⋆) = N`, so `∑_s P(s) = N/N = 1`.
    -- Split the sum at `s = s⋆` (one point) vs. the other `N-1` points. Prop 4.1.

/-- Paper XII, Proposition 4.1 (density in closed form): the density of
`deltaLaw sstar` w.r.t. uniform is the two-level field
`X_δ(s) = if s = s⋆ then A else B`. -/
lemma dens_deltaLaw (sstar s : Point n) :
    dens (deltaLaw sstar) s = if s = sstar then deltaA n else deltaB n := by
  have hN : (N n : ℝ) ≠ 0 := N_ne_zero n
  simp only [dens, deltaLaw]
  rw [mul_div_cancel₀ _ hN]  -- TODO(api): verify `mul_div_cancel₀ : b ≠ 0 → b * (a / b) = a`

/-! ## Section-3 interface: unique calibrated law `P_ε` and the gap `ŵm` -/

/-- Paper XII, Theorem 3.1 (existence and uniqueness).  Every orientation has
exactly one calibrated law `P_ε` (the unique minimizer of the strictly convex
coercive `G_ε`). -/
theorem exists_unique_calibrated (ε : Orientation n) :
    ∃! P : ProbLaw n, Calibrated P ε := by
  sorry
  -- `G_ε(ℓ) = F(ℓ) + ∑_{a≠0} e^{-ε_a ℓ_a}` is smooth, strictly convex, coercive;
  -- its unique minimizer's critical equations are exactly the calibration
  -- conditions (Definition 1.1).  Cf. Theorem 3.1.

-- `calLaw`, `calLaw_calibrated`, `mhat`, `Ddelta` are canonical in `Calibration`
-- (imported).  `calLaw_unique` is not in `Calibration`, so keep it here:
/-- Paper XII, Theorem 3.1: any calibrated law for `ε` equals `P_ε = calLaw ε`. -/
lemma calLaw_unique (ε : Orientation n) {P : ProbLaw n} (hP : Calibrated P ε) :
    P = calLaw ε :=
  (exists_unique_calibrated ε).unique hP (calLaw_calibrated ε)

/-! ## Lemma 3.2 (translation covariance), the part §4 uses -/

/-- Paper XII, Lemma 3.2.  The translated orientation `(τ_t ε)_a = ε_a χ_a(t)`.
-/
def tauOrient (t : Point n) (ε : Orientation n) : Orientation n where
  sign := fun a => ε.sign a * chi a.1 t
  is_sign := by
    intro a
    rcases ε.is_sign a with h | h <;> rcases chi_mem a.1 t with g | g <;>
      rw [h, g] <;> norm_num

/-- Paper XII, Lemma 3.2: `P_{τ_t ε}(s) = P_ε(s + t)`. -/
theorem calLaw_tauOrient (t : Point n) (ε : Orientation n) (s : Point n) :
    (calLaw (tauOrient t ε)).P s = (calLaw ε).P (s + t) := by
  sorry
  -- With `ℓ'_a = ℓ_a χ_a(t)`: `F(ℓ') = F(ℓ)` and `P_{ℓ'}(s) = P_ℓ(s+t)`, and the
  -- barrier sums match, so `G_{τ_t ε}(ℓ') = G_ε(ℓ)`; the linear bijection
  -- `ℓ ↦ ℓ'` carries the minimizer to the minimizer.  Cf. Lemma 3.2.

/-- Paper XII, Lemma 3.2: `ŵm(τ_t ε) = ŵm(ε)` (relative entropy to the
translation-invariant `U` is unchanged by a translate). -/
theorem mhat_tauOrient (t : Point n) (ε : Orientation n) :
    mhat (tauOrient t ε) = mhat ε := by
  sorry
  -- `P_{τ_t ε}` is a translate of `P_ε` (calLaw_tauOrient) and `U` is
  -- translation-invariant, so `D(·‖U)` agrees.  Cf. Lemma 3.2.

/-- Paper XII, Lemma 3.2 (delta orbit): `τ_t (ε⋆ at s⋆) = ε⋆ at s⋆ + t`; the
`N` delta orientations form a single translation orbit. -/
theorem tauOrient_deltaOrientation (t sstar : Point n) :
    tauOrient t (deltaOrientation sstar) = deltaOrientation (sstar + t) := by
  apply Orientation.ext
  intro a
  show (- chi a.1 sstar) * chi a.1 t = - chi a.1 (sstar + t)
  rw [chi_right_add]
  ring

/-! ## Proposition 4.1: the calibrated law of the delta orientation -/

/-- Paper XII, Proposition 4.1.  The two-level law `deltaLaw sstar` IS calibrated
for the delta orientation at `s⋆` (with all tilts equal, `h_a = -log u⋆ > 0`).
-/
theorem calibrated_deltaLaw (sstar : Point n) (hn : 2 ≤ n) :
    Calibrated (deltaLaw sstar) (deltaOrientation sstar) := by
  sorry
  -- Reduce to `s⋆ = 0` (Lemma 3.2): there `ε⋆ ≡ -1`, `x_a = -u⋆`, and Walsh
  -- inversion (`sum_nonzero_chi`) gives `X(s) = 1 - u⋆(N·1_{s=0} - 1)`, i.e. the
  -- two levels `A, B`.  The log-side calibration `loĝX(a) = log u⋆` is
  -- `(1-(N-1)u⋆)/(1+u⋆) = u⋆^N`, i.e. `p(u⋆) = 0` (deltaPoly_root_iff +
  -- deltaPoly_uStar).  Cf. Proposition 4.1.

/-- Paper XII, Proposition 4.1: consequently `deltaLaw sstar` is THE calibrated
law of the delta orientation, `P_{ε⋆} = deltaLaw sstar` (Theorem 3.1
uniqueness). -/
theorem calLaw_deltaOrientation (sstar : Point n) (hn : 2 ≤ n) :
    calLaw (deltaOrientation sstar) = deltaLaw sstar :=
  (calLaw_unique (deltaOrientation sstar) (calibrated_deltaLaw sstar hn)).symm

/-- Paper XII, Proposition 4.1: hence `ŵm(ε⋆) = D(deltaLaw ‖ U)`. -/
theorem mhat_deltaOrientation (sstar : Point n) (hn : 2 ≤ n) :
    mhat (deltaOrientation sstar) = Dkl (deltaLaw sstar) := by
  unfold mhat
  rw [calLaw_deltaOrientation sstar hn]

/-! ## The delta gap `D_δ` and its closed form (Prop 4.1) -/

-- `Ddelta` is canonical in `Calibration` (imported).

/-- Paper XII, Proposition 4.1 (closed form):
`D_δ = (1/N)[A log A + (N-1) B log B]` with `A = 1-(N-1)u⋆`, `B = 1+u⋆`. -/
theorem Ddelta_closedForm (n : ℕ) (hn : 2 ≤ n) :
    Ddelta n
      = (deltaA n * Real.log (deltaA n)
          + ((N n : ℝ) - 1) * (deltaB n * Real.log (deltaB n))) / (N n : ℝ) := by
  sorry
  -- `Ddelta n = D(deltaLaw 0 ‖ U) = E_U[X log X] = (1/N) ∑_s X(s) log X(s)`;
  -- `dens_deltaLaw` gives one point at level `A` and `N-1` points at level `B`.
  -- Cf. Proposition 4.1 (formula for `D_δ`).

/-! ## Symmetry Lemma 3.2: all `N` delta orientations share `D_δ` -/

/-- Paper XII, Lemma 3.2 / §4 remark: all `N` delta orientations share the single
value `D_δ`, since they form one translation orbit and `ŵm` is
translation-invariant. -/
theorem mhat_deltaOrientation_const (sstar : Point n) :
    mhat (deltaOrientation sstar) = Ddelta n := by
  have h := mhat_tauOrient sstar (deltaOrientation (0 : Point n))
  rw [tauOrient_deltaOrientation, zero_add] at h
  exact h

/-! ## Lemma 4.2: the elementary delta bound -/

/-- Paper XII, Lemma 4.2: `D_δ > 0` (the calibrated delta law is not uniform). -/
theorem Ddelta_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Ddelta n := by
  sorry
  -- A calibrated law is never uniform (Section 1.1), so `D(P‖U) > 0`.  Lemma 4.2.

/-- Paper XII, Lemma 4.2: `D_δ < 1/(N-1)`.  (From `A log A ≤ 0`,
`log(1+u⋆) ≤ u⋆`, and `1 + u⋆ < N/(N-1)`.) -/
theorem Ddelta_lt (n : ℕ) (hn : 2 ≤ n) : Ddelta n < 1 / ((N n : ℝ) - 1) := by
  sorry
  -- `A ∈ (0,1)` ⇒ `A log A ≤ 0`, so
  -- `D_δ ≤ ((N-1)/N)(1+u⋆)log(1+u⋆) ≤ ((N-1)/N)u⋆(1+u⋆)`;
  -- then `u⋆ < 1/(N-1)` and `1+u⋆ < N/(N-1)` give
  -- `D_δ < ((N-1)/N)(1/(N-1))(N/(N-1)) = 1/(N-1)`.  Lemma 4.2.

/-- Paper XII, Lemma 4.2 (statement as in the paper): `0 < D_δ < 1/(N-1)` for
every `n ≥ 2`. -/
theorem Lemma_4_2 (n : ℕ) (hn : 2 ≤ n) :
    0 < Ddelta n ∧ Ddelta n < 1 / ((N n : ℝ) - 1) :=
  ⟨Ddelta_pos n hn, Ddelta_lt n hn⟩

/-- Paper XII, Lemma 4.2 (remark): the bound is asymptotically tight,
`N·D_δ → 1` as `n → ∞`.  (From `p(u⋆) = 0` one gets
`u⋆ = (1/(N-1))(1 - O(N^{-N}))`, whence `N·D_δ → 1`.) -/
theorem N_Ddelta_tendsto_one :
    Tendsto (fun n : ℕ => (N n : ℝ) * Ddelta n) atTop (𝓝 1) := by
  sorry
  -- `u⋆ = (1/(N-1))(1 - O(N^{-N}))`, `A → 0`, `B → 1`, and
  -- `N·D_δ = A log A + (N-1)B log B → 1`.  Cf. §4 first remark after Lemma 4.2.

end WalshDelta
