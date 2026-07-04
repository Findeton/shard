import Mathlib
import WalshDelta.Basic
import WalshDelta.Calibration

/-!
# Walsh–delta: structure of low-entropy laws and the deep-dip trichotomy

Formalization of **Sections 5 and 6** of Paper XII,

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube".

Throughout, `P` is the calibrated law of an orientation `ε`, `X = dens P = N·P`,
`D = Dkl P ≤ 1/60`, and all decimal constants are safe-rounded exactly as in the
paper.

## What this file provides

* the dip / bulk / spike decomposition of the cube by the value of `X`
  (Section 5, "The dip/bulk/spike decomposition"): `dipSet`, `bulkSet`,
  `spikeSet`, the depth `depth s = -log X(s)`, and the **dip transform**
  `dipTransform a = ∑_{s ∈ 𝒮} β_s χ_a(s) = Φ(a)`;
* `Lemma 5.1` (parameter floor), `Lemma 5.2` (bookkeeping, including the
  calculus fact `|log x| ≤ 2|x-1|` on `[1/2,2]`), `Proposition 5.3` (spectral
  floor and sign readout: `|Φ(a)| ≥ N(h_min - ε_G) > 1.24416 N` and
  `ε_a = -sgn Φ(a)`), `Proposition 5.4` (dominance criterion);
* the shallow-depth bound `Σ_sh < 0.543149 N`, and `Theorem 6.1` (deep-dip
  trichotomy), with the cases `m = 0, 1, 2` isolated as sub-lemmas carrying the
  paper's numbers.

Every substantial proof is left as `sorry` with a one-line sketch citing the
paper statement it discharges.  The finite/numeric facts are stated as theorems
and `sorry`-ed; they are to be discharged by exact rational interval arithmetic,
never by `native_decide`.
-/

namespace WalshDelta

open scoped BigOperators

open Classical

variable {n : ℕ}

/-! ## Calibration data with an explicit parameter vector

`Calibrated P ε` (Basic.lean) is `∃ h, …`.  Section 5 works with a fixed choice
of the calibration parameters `h = (h_a)_{a≠0}`; `CalibratedWith P ε h` names the
body of that existential so lemmas may refer to `h_a` and `h_min` directly. -/

/-- Paper XII, Definition 1.1 (calibration with named parameters).  The body of
`Calibrated P ε` for the specific parameter vector `h`. -/
def CalibratedWith (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ) :
    Prop :=
  (∀ s, P.P s = Real.exp (tilt ε h s) / (∑ r, Real.exp (tilt ε h r)))
    ∧ (∀ a : NonzeroMask n,
        EP P (fun s => ε.sign a * chi a.1 s) = Real.exp (- h a))

/-- Paper XII, Definition 1.1: `P` is calibrated for `ε` iff it is calibrated
with *some* parameter vector `h`. -/
lemma calibrated_iff (P : ProbLaw n) (ε : Orientation n) :
    Calibrated P ε ↔ ∃ h : NonzeroMask n → ℝ, CalibratedWith P ε h := Iff.rfl

-- `IsDelta` is canonical in `Basic` (imported).

/-- `IsDelta ε` unpacked against `deltaOrientation` (the bridge from Basic's
equality form `ε = deltaOrientation s⋆` to the sign form). -/
lemma isDelta_iff (ε : Orientation n) :
    IsDelta ε ↔ ∃ sstar : Point n,
      ∀ a : NonzeroMask n, ε.sign a = (deltaOrientation sstar).sign a := by
  unfold IsDelta
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨s, fun _ => rfl⟩
  · rintro ⟨s, hs⟩; exact ⟨s, Orientation.ext hs⟩

/-! ## The minimum parameter `h_min` -/

/-- Paper XII, Section 5.  `h_min = min_{a≠0} h_a` (the smallest calibration
parameter; the minimum ranges over the nonempty finite set of nonzero masks). -/
noncomputable def hMin [Nonempty (NonzeroMask n)] (h : NonzeroMask n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty h

/-- Paper XII, Section 5: `h_min ≤ h_a` for every nonzero mask `a`. -/
lemma hMin_le [Nonempty (NonzeroMask n)] (h : NonzeroMask n → ℝ)
    (a : NonzeroMask n) : hMin h ≤ h a :=
  Finset.inf'_le _ (Finset.mem_univ a)  -- TODO(api): confirm `Finset.inf'_le`.

/-! ## The dip / bulk / spike decomposition (Section 5) -/

/-- Paper XII, Section 5 (dips).  `𝒮 = {s : X(s) ≤ 1/2}`. -/
noncomputable def dipSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => dens P s ≤ 1/2)

/-- Paper XII, Section 5 (bulk).  `𝒯 = {s : 1/2 < X(s) ≤ 2}`. -/
noncomputable def bulkSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => 1/2 < dens P s ∧ dens P s ≤ 2)

/-- Paper XII, Section 5 (spikes).  `𝒮' = {s : X(s) > 2}`. -/
noncomputable def spikeSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => 2 < dens P s)

/-- Paper XII, Section 5.  The **depth** of a dip, `β_s = -log X(s) ≥ log 2`
(finite, since calibrated laws have full support). -/
noncomputable def depth (P : ProbLaw n) (s : Point n) : ℝ := - Real.log (dens P s)

/-- Paper XII, Section 5.  The spike excess `ν_s = X(s) - 1`. -/
noncomputable def spikeExcess (P : ProbLaw n) (s : Point n) : ℝ := dens P s - 1

/-- Paper XII, Section 5.  The spike log `γ_s = log X(s)`. -/
noncomputable def spikeLog (P : ProbLaw n) (s : Point n) : ℝ := Real.log (dens P s)

/-- Paper XII, Section 5.  `k = |𝒮|`, the number of dips. -/
noncomputable def dipCount (P : ProbLaw n) : ℕ := (dipSet P).card

/-- Paper XII, Section 5 (dip transform).
`Φ(a) = ∑_{s ∈ 𝒮} β_s χ_a(s)` for `a ∈ 𝔽₂ⁿ` (with `Φ ≡ 0` if `𝒮 = ∅`). -/
noncomputable def dipTransform (P : ProbLaw n) (a : Point n) : ℝ :=
  ∑ s ∈ dipSet P, depth P s * chi a s

/-- Paper XII, Section 5.  The Walsh coefficient of `log X`,
`widehat{log X}(a) = (1/N) ∑_s log X(s) χ_a(s) = E_U[log X · χ_a]`. -/
noncomputable def logXhat (P : ProbLaw n) (a : Point n) : ℝ :=
  xhat (fun s => Real.log (dens P s)) a

/-- Paper XII, Proposition 5.3.  The Gibbs error scale `ε_G = (5/2)√(2D)`
(so that `ε_G ≤ (5/2)√(1/30) < 0.45644` when `D ≤ 1/60`). -/
noncomputable def epsG (P : ProbLaw n) : ℝ := (5/2) * Real.sqrt (2 * Dkl P)

/-- Paper XII, Proposition 5.3(ii).  The floor constant
`h' = (1/2)log 30 - (5/2)√(1/30) = 1.244163…`, the common worst case (at
`D = 1/60`) of the decreasing `(1/2)log(1/2D)` and the increasing `(5/2)√(2D)`. -/
noncomputable def hPrime : ℝ := (1/2) * Real.log 30 - (5/2) * Real.sqrt (1/30)

/-! ## Auxiliary identities and `ψ` values -/

/-- Paper XII, Lemma 2.2 / Section 2: `N·D = ∑_s ψ(X(s))`. -/
lemma N_mul_Dkl (P : ProbLaw n) :
    (N n : ℝ) * Dkl P = ∑ s, psi (dens P s) := by
  rw [Dkl_eq_EU_psi]
  simp only [EU]
  rw [mul_comm, div_mul_cancel₀ _ (N_ne_zero n)]
  -- TODO(api): confirm `div_mul_cancel₀` signature (a / b * b = a for b ≠ 0).

/-- Paper XII, Lemma 5.2(i): `ψ(1/2) = (1 - log 2)/2 = 0.153426…`. -/
lemma psi_half : psi (1/2 : ℝ) = (1 - Real.log 2) / 2 := by
  have hlog : Real.log (1/2 : ℝ) = - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  unfold psi
  rw [hlog]; ring

/-- Paper XII, Theorem 6.1: `ψ(e^{-5}) = 1 - 6 e^{-5}` (deep-dip contribution). -/
lemma psi_exp_neg5 : psi (Real.exp (-5)) = 1 - 6 * Real.exp (-5) := by
  unfold psi
  rw [Real.log_exp]; ring

/-! ## Lemma 5.1 (parameter floor) -/

/-- Paper XII, Lemma 5.1 (parameter floor).  For the calibrated law with
parameters `h` and `D = Dkl P ≤ 1/60`, every nonzero mask `a` satisfies
`|x_a| ≤ √(2D)` and `h_a ≥ (1/2)log(1/2D) ≥ (1/2)log 30 > 1.70059`
(here `x_a = xhat (dens P) a`). -/
lemma parameter_floor (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (a : NonzeroMask n) :
    |xhat (dens P) a.1| ≤ Real.sqrt (2 * Dkl P)
    ∧ (1/2) * Real.log (1 / (2 * Dkl P)) ≤ h a
    ∧ (1.70059 : ℝ) < h a := by
  sorry
  -- `|x_a| = |E_U[(X-1)χ_a]| ≤ E_U|X-1| ≤ √(2D)` by Pinsker (`pinsker`).  Calibration
  -- gives `|x_a| = e^{-h_a}`, so `h_a ≥ -log√(2D) = (1/2)log(1/2D)`; `D ≤ 1/60`
  -- gives `≥ (1/2)log 30 = 1.700598… > 1.70059`.  Cf. Lemma 5.1.

/-! ## Lemma 5.2 (bookkeeping) -/

/-- Paper XII, Lemma 5.2(iii) (calculus fact).  `|log x| ≤ 2|x-1|` on `[1/2,2]`. -/
lemma log_abs_le_two_abs_sub_one {x : ℝ} (h1 : (1:ℝ)/2 ≤ x) (h2 : x ≤ 2) :
    |Real.log x| ≤ 2 * |x - 1| := by
  have hx : (0:ℝ) < x := by linarith
  by_cases hle : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hle), abs_of_nonneg (by linarith : (0:ℝ) ≤ x - 1)]
    have := Real.log_le_sub_one_of_pos hx
    linarith
  · have hlt : x < 1 := not_le.mp hle
    rw [abs_of_neg (Real.log_neg hx hlt), abs_of_neg (by linarith : x - 1 < 0)]
    have hinv : (0:ℝ) < 1 / x := by positivity
    have hlog := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_div one_ne_zero hx.ne', Real.log_one] at hlog
    have hx2 : 1 / x ≤ 2 := by rw [div_le_iff₀ hx]; linarith
    have hprod : (2 * x - 1) * (1 - x) ≥ 0 := mul_nonneg (by linarith) (by linarith)
    have hxx : 1 / x - 1 ≤ 2 - 2 * x := by
      rw [div_sub_one hx.ne', div_le_iff₀ hx]; nlinarith [hprod]
    linarith

/-- Paper XII, Lemma 5.2 (bookkeeping).  With `D = Dkl P ≤ 1/60` and
`ε := √(2D)`:

* (i) `k ≤ DN/ψ(1/2) < 0.108630 N` (with `ψ(1/2) = (1-log 2)/2 = 0.153426…`);
* (ii) `∑_{𝒮'} γ_s ≤ ∑_{𝒮'} ν_s ≤ Nε/2`;
* (iii) `(1/N) ∑_{𝒯} |log X| ≤ 2ε`. -/
lemma bookkeeping (P : ProbLaw n) (hD : Dkl P ≤ 1/60) :
    -- (i)
    ((dipCount P : ℝ) ≤ Dkl P * (N n : ℝ) / psi (1/2)
        ∧ (dipCount P : ℝ) < 0.108630 * (N n : ℝ))
    -- (ii)
    ∧ (∑ s ∈ spikeSet P, spikeLog P s ≤ ∑ s ∈ spikeSet P, spikeExcess P s
        ∧ ∑ s ∈ spikeSet P, spikeExcess P s ≤ (N n : ℝ) * Real.sqrt (2 * Dkl P) / 2)
    -- (iii)
    ∧ (1 / (N n : ℝ)) * (∑ s ∈ bulkSet P, |Real.log (dens P s)|)
        ≤ 2 * Real.sqrt (2 * Dkl P) := by
  sorry
  -- (i) each dip has `X ≤ 1/2 < 1`, `ψ` decreasing on `[0,1]` (`psi_strictAntiOn`),
  --     so `ψ(X) ≥ ψ(1/2)`; summing into `ND = ∑ ψ(X)` gives `k ψ(1/2) ≤ ND`, and
  --     `1/(60 ψ(1/2)) = 0.1086297… < 0.108630`.
  -- (ii) `log(1+ν) ≤ ν`; `∑_{𝒮'} ν_s ≤ N·E_U(X-1)_+ = (N/2)E_U|X-1| ≤ Nε/2` (Pinsker
  --      + mean matching `E_U[X]=1`).
  -- (iii) `log_abs_le_two_abs_sub_one` gives `|log X| ≤ 2|X-1|` on `𝒯`, then
  --       `∑_{𝒯} ≤ 2N·E_U|X-1| ≤ 2Nε`.  Cf. Lemma 5.2.

/-! ## Proposition 5.3 (spectral floor and sign readout) -/

/-- Paper XII, Proposition 5.3 (spectral floor and sign readout).  With
`ε_G = (5/2)√(2D)` and `D = Dkl P ≤ 1/60` (so `ε_G < 0.45644` and
`h_min > 2ε_G`), for every nonzero mask `a`:

* (i) `|widehat{log X}(a) + Φ(a)/N| ≤ ε_G`;
* (ii) `|Φ(a)| ≥ N(h_min - ε_G) > 1.24416 N`;
* (iii) `ε_a = -sgn Φ(a)`. -/
lemma spectral_floor [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (a : NonzeroMask n) :
    -- (i)
    |logXhat P a.1 + dipTransform P a.1 / (N n : ℝ)| ≤ epsG P
    -- (ii)
    ∧ (N n : ℝ) * (hMin h - epsG P) ≤ |dipTransform P a.1|
    ∧ (1.24416 : ℝ) * (N n : ℝ) < |dipTransform P a.1|
    -- (iii)
    ∧ ε.sign a = - Real.sign (dipTransform P a.1) := by
  sorry
  -- (i) split `widehat{log X}(a)` over 𝒮/𝒯/𝒮'; the dip part is exactly `-Φ(a)/N`,
  --     the spike part `≤ ε/2` (Lemma 5.2(ii)) and the bulk part `≤ 2ε` (Lemma 5.2(iii)),
  --     total error `(5/2)ε = ε_G`.
  -- (ii) calibration `|widehat{log X}(a)| = h_a ≥ h_min` (Lemma 5.1), so by (i)
  --      `|Φ(a)|/N ≥ h_min - ε_G`; `hPrime = h_min - ε_G` worst case at D=1/60 gives `> 1.24416`.
  -- (iii) since `|Φ(a)|/N ≥ h_min - ε_G > ε_G`, `-Φ(a)/N` dominates the error in (i),
  --       so `sgn widehat{log X}(a) = -sgn Φ(a)`; and `widehat{log X}(a)=ε_a h_a`, `h_a>0`.
  --       Cf. Proposition 5.3.

/-- Paper XII, Proposition 5.3(ii): the floor constant beats `1.244163`
(`h' = 1.244163…`; certified numeric bound). -/
lemma hPrime_gt : (1.244163 : ℝ) < hPrime := by
  sorry
  -- `hPrime = (1/2)log 30 - (5/2)√(1/30) = 1.2441639…`; to be discharged by exact
  -- rational interval arithmetic (NOT by native_decide).  Cf. Proposition 5.3(ii).

/-- Paper XII, Proposition 5.3(ii): at `D ≤ 1/60`, `h_min - ε_G ≥ h'`.
Both `(1/2)log(1/2D)` (decreasing) and `(5/2)√(2D)` (increasing) are worst at
`D = 1/60`. -/
lemma hMin_sub_epsG_ge_hPrime [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) :
    hPrime ≤ hMin h - epsG P := by
  sorry
  -- `h_min ≥ (1/2)log(1/2D) ≥ (1/2)log 30` (Lemma 5.1) and
  -- `ε_G = (5/2)√(2D) ≤ (5/2)√(1/30)`; subtract.  Cf. Proposition 5.3(ii).

/-- Paper XII, Proposition 5.3(ii)–(iii): `Φ(a) ≠ 0` for every `a ≠ 0`; in
particular `𝒮 ≠ ∅` automatically. -/
lemma dipTransform_ne_zero [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (a : NonzeroMask n) :
    dipTransform P a.1 ≠ 0 := by
  sorry
  -- `|Φ(a)| ≥ N(h_min - ε_G) ≥ N·hPrime > 1.244163 N > 0`.  Cf. Proposition 5.3(ii).

/-! ## Proposition 5.4 (dominance criterion) -/

/-- Paper XII, Proposition 5.4 (dominance criterion).  If some dip `s₁ ∈ 𝒮`
carries at least half the total depth,
`β_{s₁} ≥ ∑_{s ∈ 𝒮 ∖ {s₁}} β_s`, then `ε` is the delta orientation at `s₁`
(`ε_a = -χ_a(s₁)` for every `a ≠ 0`). -/
lemma dominance_criterion [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60)
    (s₁ : Point n) (hs₁ : s₁ ∈ dipSet P)
    (hdom : (∑ s ∈ (dipSet P).erase s₁, depth P s) ≤ depth P s₁) :
    ∀ a : NonzeroMask n, ε.sign a = - chi a.1 s₁ := by
  sorry
  -- Write `Φ(a) = β_{s₁} χ_a(s₁) + R(a)` with `|R(a)| ≤ ∑_{s≠s₁} β_s ≤ β_{s₁}`.  Then
  -- `χ_a(s₁)Φ(a) = β_{s₁} + χ_a(s₁)R(a) ≥ 0`, and equality would force `Φ(a)=0`, excluded
  -- by `dipTransform_ne_zero` (Prop 5.3(ii)).  Hence `sgn Φ(a) = χ_a(s₁)`, and Prop 5.3(iii)
  -- gives `ε_a = -χ_a(s₁)`.  Cf. Proposition 5.4.

/-! ## Section 6: deep dips, the shallow-depth bound, and the trichotomy -/

/-- Paper XII, Theorem 6.1 (deep dips).  `{s : X(s) ≤ e^{-5}}` (equivalently
`β_s ≥ 5`). -/
noncomputable def deepDipSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => dens P s ≤ Real.exp (-5))

/-- Paper XII, Theorem 6.1.  `m = |{s : X(s) ≤ e^{-5}}|`, the number of deep dips. -/
noncomputable def deepDipCount (P : ProbLaw n) : ℕ := (deepDipSet P).card

/-- Paper XII, Theorem 6.1 (shallow dips).  Dips that are not deep,
`{s ∈ 𝒮 : X(s) > e^{-5}}` (`β_s < 5`). -/
noncomputable def shallowDipSet (P : ProbLaw n) : Finset (Point n) :=
  (dipSet P).filter (fun s => Real.exp (-5) < dens P s)

/-- Paper XII, Theorem 6.1.  The shallow total depth
`Σ_sh = ∑_{shallow s} β_s`. -/
noncomputable def shallowDepthSum (P : ProbLaw n) : ℝ :=
  ∑ s ∈ shallowDipSet P, depth P s

/-- Paper XII, Theorem 6.1 (shallow-depth bound).
`Σ_sh < 5k ≤ 5N/(60 ψ(1/2)) < 0.543149 N`. -/
lemma shallowDepthSum_lt (P : ProbLaw n) (hD : Dkl P ≤ 1/60) :
    shallowDepthSum P < 0.543149 * (N n : ℝ) := by
  sorry
  -- Each shallow dip has `β_s < 5`, so `Σ_sh < 5k`; `k ≤ N/(60 ψ(1/2))` (Lemma 5.2(i))
  -- and `5/(60 ψ(1/2)) = 0.543148…  < 0.543149`.  Cf. Theorem 6.1.

/-- Paper XII, Theorem 6.1: `3ψ(e^{-5}) = 3(1 - 6e^{-5}) > 2.878716` (certified
numeric bound). -/
lemma three_psi_exp_neg5_gt : (2.878716 : ℝ) < 3 * (1 - 6 * Real.exp (-5)) := by
  sorry
  -- `3(1 - 6e^{-5}) = 2.8787169…`; to be discharged by exact rational interval
  -- arithmetic (NOT by native_decide).  Cf. Theorem 6.1.

/-! ### Ruling out `m ≤ 2` (the three cases of Theorem 6.1) -/

/-- Paper XII, Theorem 6.1, **Case `m = 0`**.  If every dip is shallow then for
any `a ≠ 0` (present since `N ≥ 4`),
`|Φ(a)| ≤ Σ_sh < 0.543149 N < 1.24416 N ≤ |Φ(a)|` — impossible.  Hence
`m ≠ 0`.  (This subsumes `k = 0`, where `Φ ≡ 0`.) -/
lemma deepDipCount_ne_zero [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    deepDipCount P ≠ 0 := by
  sorry
  -- `m = 0` ⇒ all dips shallow ⇒ `|Φ(a)| ≤ Σ_sh < 0.543149 N`, contradicting the floor
  -- `|Φ(a)| > 1.24416 N` (Prop 5.3(ii)).  Cf. Theorem 6.1, Case m=0.

/-- Paper XII, Theorem 6.1, **Case `m = 1`**.  A single deep dip `s₁` must, by
the floor `|Φ(a)| ≤ β_{s₁} + Σ_sh` and Prop 5.3(ii), satisfy
`β_{s₁} ≥ Nh' - Σ_sh > 0.701014 N > Σ_sh`, so `s₁` dominates and Prop 5.4 makes
`ε` a delta orientation — contradicting `¬ IsDelta ε`.  Hence `m ≠ 1`. -/
lemma deepDipCount_ne_one [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    deepDipCount P ≠ 1 := by
  sorry
  -- deep dip `s₁`: `|Φ(a)| ≤ β_{s₁}+Σ_sh` forces `β_{s₁} ≥ Nh'-Σ_sh > 0.701014 N > Σ_sh
  --  = ∑_{s≠s₁} β_s`, so `dominance_criterion` (Prop 5.4) ⇒ `IsDelta ε`, contradiction.
  -- Cf. Theorem 6.1, Case m=1.

/-- Paper XII, Theorem 6.1, **Case `m = 2`**.  With deep dips `s₁,s₂`
(`β_{s₁} ≥ β_{s₂}`), choosing `a` with `χ_a(s₁+s₂) = -1` (an `N/2`-set not
containing `0`) gives `|Φ(a)| ≤ |β_{s₁}-β_{s₂}| + Σ_sh`, whence
`β_{s₁}-β_{s₂} ≥ Nh'-Σ_sh > 0.701014 N`, so
`β_{s₁} - (β_{s₂}+Σ_sh) > 0.157865 N > 0`: `s₁` again dominates and Prop 5.4
gives `IsDelta ε` — contradiction.  Hence `m ≠ 2`. -/
lemma deepDipCount_ne_two [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    deepDipCount P ≠ 2 := by
  sorry
  -- deep dips `s₁,s₂` (β_{s₁}≥β_{s₂}); pick `a` with `χ_a(s₁+s₂)=-1` so `χ_a(s₂)=-χ_a(s₁)`,
  -- giving `|Φ(a)| ≤ |β_{s₁}-β_{s₂}|+Σ_sh` ⇒ `β_{s₁}-β_{s₂} > 0.701014 N` ⇒
  -- `β_{s₁} > β_{s₂}+Σ_sh` ⇒ `s₁` dominates ⇒ Prop 5.4 ⇒ `IsDelta ε`, contradiction.
  -- Cf. Theorem 6.1, Case m=2.

/-- Paper XII, Theorem 6.1 (conclusion of the case analysis).  Ruling out
`m ∈ {0,1,2}` gives `m ≥ 3`. -/
lemma deepDipCount_ge_three [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    3 ≤ deepDipCount P := by
  have h0 := deepDipCount_ne_zero hn P ε h hcal hD hnd
  have h1 := deepDipCount_ne_one hn P ε h hcal hD hnd
  have h2 := deepDipCount_ne_two hn P ε h hcal hD hnd
  omega

/-- Paper XII, Theorem 6.1 (deep-dip trichotomy).  Let `ε` be an orientation
that is **not** a delta orientation, and suppose its calibrated law has
`D = Dkl P ≤ 1/60`.  Then at least three points of the cube satisfy
`X(s) ≤ e^{-5}`, and consequently

  `N·D ≥ 3 ψ(e^{-5}) = 3(1 - 6e^{-5}) > 2.878716`.

(The hypothesis `2 ≤ n` encodes the standing `N ≥ 4` assumption of Section 5,
used to guarantee nonzero masks exist.) -/
theorem deep_dip_trichotomy [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n)
    (hcal : Calibrated P ε) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    3 ≤ deepDipCount P
    ∧ 3 * psi (Real.exp (-5)) ≤ (N n : ℝ) * Dkl P
    ∧ (2.878716 : ℝ) < (N n : ℝ) * Dkl P := by
  sorry
  -- Obtain `h` with `CalibratedWith P ε h` from `hcal`; `deepDipCount_ge_three` gives `m ≥ 3`.
  -- Each deep dip has `X(s) ≤ e^{-5} < 1`, `ψ` decreasing on `[0,1]` (`psi_strictAntiOn`), so
  -- `ψ(X(s)) ≥ ψ(e^{-5}) = 1 - 6e^{-5}` (`psi_exp_neg5`); all `ψ`-terms are `≥ 0` (`psi_nonneg`),
  -- so `N·D = ∑ ψ(X)` (`N_mul_Dkl`) `≥ 3 ψ(e^{-5}) = 3(1 - 6e^{-5}) > 2.878716`
  -- (`three_psi_exp_neg5_gt`).  Cf. Theorem 6.1.

end WalshDelta
