# Spectral-radius upper-tail deviations in Lean

Lean 4 formalization accompanying **Yi Han, [Large deviations of the spectral radius of iid subgaussian random matrices](https://arxiv.org/abs/2610.05498)**, arXiv:2610.05498 (2026).

This repository covers the paper's **upper-tail results and local complex eigenvalue deviations**. It includes the supporting concentration, coupling, resolvent, outlier, and real Gaussian estimates. The final matching-class theorems have no unproved Gaussian or concentration input.

The arXiv paper also contains lower-tail results. **The quadratic-speed lower-tail theorem and the resulting full LDP for the untruncated spectral radius are outside this repository's verified scope.** The setwise LDP formalized here is for the clipped radius `max(1, ρ)`.

## Mathematical results

For the normalized iid matrix $X_n=n^{-1/2}(\xi_{ij})$, write

$$I_\beta(r)=\frac{\beta}{2}\bigl(r^2-1-2\log r\bigr),\qquad r>1,$$

with $\beta=1$ over $\mathbb R$ and $\beta=2$ over $\mathbb C$.

- **Matching upper-tail rates.** The strict and non-strict spectral-radius tails have normalized logarithmic limit $-I_\beta(r)$ under the paper's matching-class hypotheses. For real entries these are symmetry, unit second moment, and Gaussian domination of the even moments. For complex entries they are centeredness, unit variance, zero pseudovariance, and the sharp planar Gaussian Laplace bound. Discrete entry laws are allowed.
- **Local complex eigenvalue deviations.** For an exterior disk $B(z,\varepsilon)$ with $0<\varepsilon<|z|-1$, the event that an actual eigenvalue lies in the disk has rate $-I_2(|z|-\varepsilon)$ in the complex sharp class. The iterated small-disk limit is $-I_2(|z|)$. A universal lower bound is also proved under a square-exponential moment assumption, without the sharp Laplace bound.
- **Clipped-radius LDP.** Open- and closed-set exponential bounds are proved for $\max(1,\rho(X_n))$, with rate $I_\beta$ on $[1,\infty)$ and infinite rate below one.
- **Real Gaussian inputs.** The actual normalized iid real Gaussian matrix satisfies the required Hilbert–Schmidt power upper asymptotic, sharp right-tail limits, and clipped-radius LDP. These are proved in Lean rather than assumed from an external Gaussian LDP.

The upper-deviation lower-bound machinery uses a support-preserving change of measure, an actual outlier construction, and a proved bounded-product Talagrand concentration theorem. The real upper bound uses entry-moment comparison and a proved Gaussian Schur power comparison.

## Where to start

All declarations below are in the `SpectralRadiusUpperTail` namespace. Paper theorem numbers refer to arXiv v1.

| Result | Lean entry point |
| --- | --- |
| Theorem 1.2, real matching tails | [`real_class_sharp_log_tail_limits_of_entry_hypotheses`](SpectralRadiusUpperTail/RealSharpClassUnconditional.lean) |
| Real matching exponential and clipped set bounds | [`RealSharpClassUnconditional.lean`](SpectralRadiusUpperTail/RealSharpClassUnconditional.lean) |
| Complex matching clipped set bounds | [`complex_sharp_class_clipped_deviation_bounds_of_entry_hypotheses`](SpectralRadiusUpperTail/TalagrandClassConsequences.lean) |
| Theorem 1.7, exterior-disk lower bound, exact rate, and small-disk limit | [`ComplexLocalDeviation.lean`](SpectralRadiusUpperTail/ComplexLocalDeviation.lean) |
| Real Gaussian power upper bound | [`realGaussian_power_upper_proved`](SpectralRadiusUpperTail/RealGaussianPowerUpperProved.lean) |
| Real Gaussian radius tails and clipped LDP | [`RealGaussianRadiusLDPProved.lean`](SpectralRadiusUpperTail/RealGaussianRadiusLDPProved.lean) |
| Actual real Gaussian Schur power comparison | [`RealGaussianSchurPowerComparison.lean`](SpectralRadiusUpperTail/RealGaussianSchurPowerComparison.lean) |
| Bounded-product concentration | [`cutoff_convex_concentration_proved`](SpectralRadiusUpperTail/TalagrandClassConsequences.lean) |

[`SpectralRadiusUpperTail.lean`](SpectralRadiusUpperTail.lean) imports every project module. [`AxiomAudit.lean`](AxiomAudit.lean) audits every explicitly named project declaration. Older conditional interfaces remain available, but the final entry points above supply their analytic inputs by proved theorems.

## Scope of the Gaussian formalization

The main real theorem needs an upper bound for the power moment at $k_n=\lfloor\alpha n\rfloor$. This is the statement proved by `realGaussian_power_upper_proved`. The stronger two-sided asymptotic for every sequence $k_n/n\to\alpha$ in the paper's Corollary 3.4 is not separately claimed as a formalized endpoint.

For nonreal eigenvalues, the proof establishes a weighted one-point **upper bound with a fixed constant times the dimension**. This polynomial loss does not affect the large-deviation exponent. The proof calibrates the angular mass using total root count; it does not assert the exact finite-dimensional nonreal one-point normalization formula.

This is a formalization of the stated results through explicit Lean proofs, not a line-by-line transcription of every auxiliary assertion in the paper. The proof sources were developed with assistance from OpenAI Codex; the Lean kernel checks the formal statements, not their identification with every sentence of the paper.

## Requirements and pinned dependencies

- Lean **4.33.0**, selected by [`lean-toolchain`](lean-toolchain).
- mathlib at [`db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d).
- [`ginibre-correlation-identities-lean`](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean) at [`403bab996ebc6b8331531bdf12b7a8c84bf61a4d`](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean/tree/403bab996ebc6b8331531bdf12b7a8c84bf61a4d), providing proved Schur-coordinate and measurable-spectrum results.
- Python 3.10 or later for the optional audit scripts.

Both Lean dependencies are declared in [`lakefile.toml`](lakefile.toml) and pinned in [`lake-manifest.json`](lake-manifest.json). No separate sibling checkout or machine-specific path is required.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/hanyi162013-Yihan/spectral-radius-upper-tail-lean.git
cd spectral-radius-upper-tail-lean
lake exe cache get
lake build
lake env lean AxiomAudit.lean > axioms.log
python3 scripts/check_snapshot.py --axioms-log axioms.log
```

The project is large; a first build also builds the pinned Ginibre dependency. Lean's proof-checking limits remain at their defaults. No `maxHeartbeats` or `maxRecDepth` increases are used.

After dependencies have been built, the optional sequential checker can recheck all project sources in dependency order and reject incomplete proofs or unexpected axioms:

```sh
python3 check.py
```

A selected endpoint can be rechecked against the outputs of `lake build` with:

```sh
lake env lean SpectralRadiusUpperTail/RealSharpClassUnconditional.lean
```

## Verification record

The **2026-09-26** checked snapshot contains **1,996 project modules**, **5,424 explicitly named declarations**, and **104,579 lines of project proof sources**. All **1,998 source hashes**, including the aggregate import and axiom-audit files, match passing checks. The dependency order was checked as well.

The audited axioms are subsets of Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` placeholders or project-specific axioms. Linter warnings are recorded separately from proof-checking failures.

[`verification/snapshot.json`](verification/snapshot.json) records the source hashes and historical check metadata. Machine-specific build logs and compiled artifacts are not included in the repository. To compare the checkout with that snapshot without running Lean:

```sh
python3 scripts/check_snapshot.py
```

A hash match identifies the checked source version; reproducing the proof checks requires the build and axiom-audit commands above.

## Citation

```bibtex
@article{han2026spectralradius,
  title         = {Large deviations of the spectral radius of iid subgaussian random matrices},
  author        = {Han, Yi},
  year          = {2026},
  eprint        = {2610.05498},
  archivePrefix = {arXiv},
  primaryClass  = {math.PR},
  url           = {https://arxiv.org/abs/2610.05498}
}
```
