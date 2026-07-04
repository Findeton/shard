# SORRIES — the map of open proof leaves, easiest → hardest

Every `sorry` in the development, triaged by difficulty. `theorem_1_2` depends on
`sorryAx` until Tier D's two halves (`main_equality_analytic`, `theorem_8_3`) and
everything they transitively use are discharged. Work top-down: Tier A/B are
self-contained Mathlib exercises; Tier C are real but standard; Tier D are the
two research frontiers (the analytic quantitative bounds and the certified
finite computation).

Status legend: ☐ open · ✅ done (`lake build` clean).

## Tier A — trivial (Mathlib one-liner / `ring` / `ext`)

- ✅ `Basic.card_point` — `Fintype.card (Fin n → ZMod 2) = 2^n`.
- ✅ `Basic.chi_add` — `χ_{a+b} = χ_a·χ_b` (sign homomorphism of the `𝔽₂` pairing).
- ✅ `Delta.chi_right_add` — `χ_a(s+t) = χ_a(s)·χ_a(t)` (same, in the point arg).
- ✅ `Basic.Dkl_eq_EU_psi` — `E_U[ψ(X)] = D` (algebra + `EU_dens_eq_one`).
- ✅ `Basic.xhat_dens_eq_EP` — `E_U[X χ_a] = E_P[χ_a]` (unfold `dens`, cancel `N`).
- ✅ `Delta.deltaPoly_root_iff` — expand `u^N(1+u)` and `ring`.
- ✅ `Delta.deltaA_pos` / ✅ `Delta.deltaA_lt_one` — `linarith` from `uStar_lt`/`uStar_pos`.
- ✅ `Certified.secondMomentMatrix_isSymm` — `mul_comm` inside the sum.
- ✅ `Trichotomy.isDelta_iff` — `Orientation.ext` (equality ⟺ signs agree).

## Tier B — easy (one real Mathlib lemma, a few lines)

- ✅ `Basic.psi_nonneg`, `psi_strictAntiOn`, `psi_strictMonoOn` — monotonicity of
  `ψ` from `ψ' = log` (`StrictMonoOn`/`StrictAntiOn` of-deriv; `psi_hasDerivAt`).
- ☐ `Basic.pinsker` — Mathlib information-theory Pinsker (`… .tv_le … `) + `E_U|X-1| = 2·TV`.
- ✅ `Delta.sum_chi`, `sum_nonzero_chi` — Walsh/character orthogonality on `𝔽₂ⁿ`
  (sign-flip involution `s ↦ s + eⱼ`; full-sum-minus-`a=0` via pairing symmetry).
- ☐ `Delta.deltaLaw` (pos, sum_one) — `A,B > 0`; `A + (N-1)B = N`. (Blocked: `pos`
  needs the `n<2` junk-root edge; skip until `uStar_exists_unique` extends.)
- ✅ `Delta.uStar_lt` — strict monotone `p` with `p(u⋆)=0 < p(1/(N-1))`.  ☐ `Ddelta_pos`.
- ✅ `Certified.secondMomentMatrix_psd`, `covMatrix_psd` — `vᵀMv = E[(∑vχ)²] ≥ 0`
  (closed forms `quadForm_secondMomentMatrix`, `sum_v_xcoord`; `covMatrix_psd` = Cauchy–Schwarz).
- ✅ `Certified.covMatrix_le_secondMoment` (rank-one `quadForm_covMatrix_eq`).
  ☐ `opNorm_le_trace_of_psd` — spectral theorem (really Tier D).
- ✅ `Trichotomy.log_abs_le_two_abs_sub_one` — `Real.log_le_sub_one_of_pos` on `[½,2]`.
- ✅ `Symmetry.glOrient_one`, `delta_injective` — identity action; characters separate points.
- ✅ `Symmetry.dotZ2_mulVec`, `glTransInv_mulVec_ne_zero`, `delta_glAction` — matrix
  adjunction (`dotProduct_mulVec`/`mulVec_transpose`); `(M⁻¹)ᵀ` invertible; `chi_mulVec`.

## Tier C — medium (multi-step, standard mathematics)

- ☐ `Calibration.*` convexity/coercivity cluster: `logPartition_convexOn`,
  `Gfun_strictConvexOn`, `Gfun_coercive`, `logPartition_partialDeriv`,
  `Gfun_partialDeriv`, `critical_iff_calibrationEqs`, `calibrated_of_critical`,
  `hcoeff_pos_of_critical`, `Gfun_min_exists_unique`, `ellStar_isCritical`,
  `calibrated_exists_unique`, `*_contDiff`, `logPartition_radial_tendsto`.
- ☐ `Symmetry.*` covariance cluster (remaining): `translation_covariance_law/_mhat`,
  `glAction_covariance_law/_mhat` (need the minimizer relabeling + `hP.2` uniqueness).
  [`dotZ2_mulVec`, `glTransInv_mulVec_ne_zero`, `delta_glAction` now ✅.]
- ✅ `Delta`: `deltaPoly_strictMonoOn` (monotone sum), `deltaPoly_pos_at_bound`
  (`(N-1)·1/(N-1)=1` cancels), `uStar_exists_unique` (IVT + strict mono),
  `tauOrient_deltaOrientation` (`chi_right_add`).  [These also clear `uStar_spec`,
  `uStar_pos`, `deltaPoly_uStar`, `uStar_lt` transitively.]
- ☐ `Delta` (still, gated by the `Calibration` convex core): `calLaw_tauOrient`,
  `mhat_tauOrient`, `calibrated_deltaLaw`, `Ddelta_closedForm`, `Ddelta_pos`,
  `Ddelta_lt`, `N_Ddelta_tendsto_one`, `Lemma_4_2`, `exists_unique_calibrated`,
  `deltaLaw` (pos/sum_one — `pos` needs the `n<2` junk-root edge).
- ☐ `Certified`: `exists_unique_minimizer`, `lemma_8_1`, `lemma_8_2_grad/_transfer`,
  `Ddelta_eq`, `mhat_transOrient/_glOrient/_of_sameOrbit`, `isDelta_of_sameOrbit`,
  `nat_card_orientation`.

## Tier D — hard (the two frontiers + the numeric constants)

- ☐ **Analytic frontier** (`Trichotomy` §5–6 + `AnalyticMain` §7):
  `parameter_floor`, `bookkeeping`, `spectral_floor`, `hMin_sub_epsG_ge_hPrime`,
  `dipTransform_ne_zero`, `dominance_criterion`, `shallowDepthSum_lt`,
  `deepDipCount_ne_zero/_one/_two`, `deep_dip_trichotomy`;
  `main_analytic`, `corollary_1_3`, `main_equality_analytic`,
  `translation_covariance`, `tau_deltaOrientation`, `N_Ddelta_tendsto_one`,
  `Main.corollary_1_3_top`.
- ☐ **Numeric constants** (rigorous rational/interval arithmetic, NOT `norm_num`
  on transcendentals): `three_psi_gt`, `hPrime_gt`, `three_psi_exp_neg5_gt`.
- ☐ **Certified frontier** (`Certified` §8): `theorem_8_3`, `orbitCount_five`,
  `orbitCount_low`, `reduce_to_transversal` — the exact-interval Newton–Kantorovich
  certification over the 176-orbit Γ₅ transversal.

---


