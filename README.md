# SHARD

SHARD says physics is made of whole histories of sealed records, not
instantaneous states. Quantum phases, spacetime, gauge structure, and
matter constraints emerge from which record distinctions can be sealed
without silent, unrecorded structure.

This repository is the program's **publishable batch**: thirteen papers
and six companion notes (markdown is the source of record throughout;
LaTeX and compiled PDF are provided for the eleven core
mathematics/foundations papers — papers X and XI and the six companion
notes ship as markdown plus receipts), the two dated registration
documents for the program's experimental claims, and the complete set
of receipt scripts with their canonical outputs.

**Author:** Felix Robles Elvira (ORCID:
[0009-0009-2017-4394](https://orcid.org/0009-0009-2017-4394);
independent researcher)

**Status:** preprints, not peer reviewed, version 2026-06-15. Nothing
in this repository has been deposited, submitted, or posted anywhere
yet; the registration documents have no evidential standing until the
batch is third-party timestamped (Zenodo deposit planned, then arXiv).

## Layout

```
papers/         the thirteen papers + six companion notes (markdown source of record)
tex/            LaTeX (generated from markdown by code/md2tex.py; eleven core papers)
pdf/            compiled PDFs (tectonic; eleven core papers)
registrations/  two dated registration documents (neutrino claims)
code/           receipt scripts + the md->tex build tool
receipts/       canonical outputs of every receipt script
```

## The thirteen papers

In-batch citation labels (used throughout the papers) map to files as
follows. `[P]` in any paper marks a dependency whose proof lives in
the larger program corpus, which is **not** part of this repository —
the papers grade every such pointer as a stated dependency, not a
verified one.

| Label | File | One line |
|---|---|---|
| [C0] | `paper-C0-binding-codes` | Exactly solvable binding theory of parity-relation codes; the marginality constant κ and ε = 3κ − 1, self-contained |
| [C1] / I | `paper-I-psd-words` | Census of words in two PSD letters: chirality, the exact d = 3 certificate, the d = 2 floor theorem, Conjecture NR |
| [C2] / II | `paper-II-rp-realization` | Reflection-positive realization, the record clock, exact peripheral reduction, the two-conjecture reduction |
| [C3] / III | `paper-III-moment-test` | The moment/clock test (v2.2): a falsifiable instrument, synthetic calibration, device verdicts |
| [C4] / IV | `paper-IV-graded-weyl` | A graded Weyl law as experimental mathematics: detector-level homogenization, the impostor, the Favard class |
| Va | `paper-Va-foundations-1` | Foundations I: Born layer, Lorentz signature, arrow of time; the full input/audit discipline |
| Vb | `paper-Vb-foundations-2` | Foundations II: univalence superselection, statistics from framed transport, Schur–Weyl commutant groups |
| VI | `paper-VI-sm-floor` | Standard-Model floor: hypercharge as relative determinant character, charge screening, the uniqueness searches |
| [C-VIII] / VIII | `paper-VIII-horizons` | Horizons on record lattices: temperature two ways, greybody closed form, capacity at c/6 |
| [VII] | `paper-VII-neutrino-note` | Registration record: the undressed neutrino spectrum point against JUNO, with full correction history |
| [IX] | `paper-IX-fn-mechanism` | Froggatt–Nielsen-type mechanism with derived suppression: two theorems, an obstruction by conjunction, a discrete four-member neutrino menu (two live) |
| X | `paper-X-gravitational-decoherence` | Gravitational decoherence does not certify its mechanism: the Gaussian onset is mechanism-blind, irreversible sealing is CP-divisible, and the structural indivisibility is operationally undecidable from the reduced channel |
| XI | `paper-XI-sealed-record-gravity-no-go` | Emergent Einstein equations without an emergent Newton constant: the gravitational equation of state is derived (modulo named gates); the absolute scale G is a weight-counting no-go |

Suggested reading order: the mathematics first (I, II, C0, IV), then
the instrument and the cleanest physics (III, VIII), then the
framework (Va, Vb, VI), and last the empirical surface (VII and IX
together — VII is the registration record, IX the mechanism; the
bare-point vs dressed-menu two-claim structure is deliberate and the
two documents cross-declare each other). Papers X and XI are the
gravity pair: XI derives the gravitational equation of state and proves
the scale no-go on Newton's `G`, and X is its observational counterpart
(why gravitational decoherence cannot certify its own mechanism).

## Companion notes

Six shorter notes attach to the papers above. Each is explicitly
*program-internal*: it states up front what is standard external
machinery (invoked, not claimed) and what the contribution about the
records is — a positioning, a no-go, or a named gate. They ship as
markdown source plus receipts (no separate LaTeX/PDF).

| Note | Attaches to | One line |
|---|---|---|
| `companion-A-entropic-clock` | Va | The forced survival law on the records' internal entropic clock: exponential along dense chains, multiplicative across sparse ones, with the Born/self-consistency/odometer supports it rests on |
| `companion-B-almost-quantum` | Va / Vb | Transverse record correlations are a moment-positivity condition landing on the **almost-quantum set** `Q̃`; the gap `Q̃ ∖ Q` is permanent because the records host no composite state space (tensor product, local tomography) |
| `companion-D-conformal-direction` | XI | Order owns the conformal **direction** (scale-free), the seal **count** owns the volume up to `l_step`, and **manifoldlikeness** is the field-shared gate — the continuum companion to the gravity no-go |
| `companion-E-covariant-decoherence` | X | Covariantizing the record decoherence layer; the derived-noise-kernel type-mismatch no-go against a naive geometric identification |
| `companion-F-chiral-matter` | VI | The record chiral-matter machinery (the PSG ingredient functor, the closed chiral-gap law) and two chirality no-gos |
| `companion-G-scale-grading` | XI | The weight-grading no-go across the program's scales (`d`, `G`, the `c_m` hierarchy): why no record functional supplies an absolute length |

## Registrations

`registrations/` holds the two dated registration documents:

- `registered-prediction-neutrino-step.md` — the undressed spectrum
  point (Paper VII's claim), with its cumulative correction record.
- `registered-prediction-lepton-mixing-cp.md` — the mechanism-derived
  claim set (Paper IX's menu), including the withdrawn items, kept
  visible per the program's correction discipline.

Both documents say so themselves: until the batch is deposited with a
third-party timestamp they have no standing beyond this repository's
own dating.

## Code and receipts

Every quantitative claim in the papers regenerates from a
deterministic, fixed-seed script whose reruns are bit-identical — with
one disclosed exception: the CHSH semidefinite program in
`t1_npa_q_vs_qtilde` (companion B) is reproducible only to SCS solver
tolerance (~10⁻⁹), so its Tsirelson-value line can differ in the last
digit between runs. The load-bearing claim there is that the SDP
maximum equals the *analytic* `2√2`, which is what companion B cites;
the last printed digit is solver noise, not a derived figure. Scripts
write their canonical output to `/tmp/<name>.out`; the `receipts/`
directory holds those canonical outputs. To check one:

```
pip install -r requirements.txt
python3 code/<script>.py > /tmp/<name>.out
diff /tmp/<name>.out receipts/<name>.out      # must be empty
```

Per-paper receipt map (script names in `code/`, outputs in
`receipts/`):

| Paper | Scripts | Canonical outputs |
|---|---|---|
| C0 | `v6_pub_c0_receipt`, `v6_p8a/b_*`, `v6_p35_*`, `v6_p36_*`, `global_frustration_optimum` (§7 global optimum) | `v6_pub_c0_receipt.out`, `p8a/b.out`, `v6_p35/36_campaign.out`, `global_frustration_optimum.out` |
| I | `v6_pub_i_certificate_receipt` (exact-rational d = 3 certificate), `v6_p30a/g/i_*` | `v6_pub_i_certificate.out`, `p30a/g/i.out` |
| II | `v6_p30a–i_*` (shared campaign with I), `v6_p16a/b_*` (clock, Heller boundary) | `p30a–i.out`, `p16a/b.out` |
| III | `clock_test_tool.py` | `clock_test_v22.out` |
| IV | `v6_p32a–c_*`, `v6_pub_iv_chat_receipt` | `p32a–c.out`, `v6_pub_iv_chat.out` |
| Va | `v6_p29a_*`, `v6_p12a–d_*`, `v6_p33a/b_*` | `p29a.out`, `p12a–d.out`, `p33a/b.out` |
| Vb | `v6_p9a–c_*`, `v6_p11a–f_*`, `v6_p18a–f_*` | `p9a–c.out`, `p11a–f.out`, `p18a–f.out` |
| VI | `v6_p31a–h_*`, `v6_p14a–e_*`, `v6_p17a/b_*` | `p31a–h.out`, `p14a–e.out`, `p17a/b.out` |
| VII | `v6_p34_coefficient_campaign` | `v6_p34_campaign.out` |
| VIII | `v6_p13a–e_*` | `p13a–e.out` |
| IX | `v6_p37_*`, `v6_p38_*`, `v6_p38b_parity_obstruction` | `v6_p37/38_campaign.out`, `v6_p38b_parity.out` |
| X | `v6_pX_decoherence_undecidability_receipts` | `v6_pX_decoherence_undecidability_receipts.out` |
| XI | `v6_pXI_sealed_record_gravity_nogo_receipts` | `v6_pXI_sealed_record_gravity_nogo_receipts.out` |

Companion notes (scripts in `code/`, outputs in `receipts/`):

| Note | Scripts | Canonical outputs |
|---|---|---|
| A (entropic clock) | `f1_born_projection_q2`, `f3_self_consistency`, `f3b/c/d/e_*`, `f4_variational_rate`, `p2a/b/c_*` | `f1_born_projection_q2.out`, `f3*.out`, `f4_variational_rate.out`, `p2a/b/c_*.out` |
| B (almost-quantum) | `t1_npa_q_vs_qtilde`, `t2_purification_uniqueness`, `t3_tsirelson_derivation` | `t1/t2/t3_*.out` |
| D (conformal direction) | `r1_order_to_conformal_direction`, `r2_number_volume_lstep`, `r3_manifoldlikeness_myrheim_meyer` | `r1/r2/r3_*.out` |
| E (covariant decoherence) | `c1_lorentz_scalar_seal_mcc`, `c2_derived_noise_kernel` | `c1/c2_*.out` |
| F (chiral matter) | `v7_m1_psg_gap_chiral_receipt`, `p9a_chiral_gap_closed`, `p9b_psg_ingredient_functor`, `p9c_chirality_bridge_nogo`, `m2_mode_canonicalization`, `global_frustration_optimum` | `v7_m1_*.out`, `p9a/b/c_*.out`, `m2_*.out`, `global_frustration_optimum.out` |
| G (scale grading) | `p3_d_nogo`, `p5_cm_calibration` | `p3_d_nogo.out`, `p5_cm_calibration.out` |

Notes:

- Paper III's device verdicts analyze the public Google surface-code
  memory dataset (Zenodo record 6804040). The dataset is **not**
  redistributed here; the canonical output of the full device run
  (`clock_test_v22.out`) is included, and re-running the synthetic
  calibration needs no external data.
- Some campaign scripts carry receipts for more than the batch quotes
  from them: the papers are distillations, and the scripts are
  included whole rather than trimmed, so every quoted number has its
  origin in-repo.

## Building the PDFs

```
python3 code/md2tex.py papers/<paper>.md tex/<paper>.tex
tectonic tex/<paper>.tex
```

The markdown files in `papers/` are the source of record; `tex/` and
`pdf/` are generated.

## License

See `LICENSE`.
