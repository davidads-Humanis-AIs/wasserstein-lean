# Wasserstein distance in Lean

A Lean 4 / mathlib library on Wasserstein distances between Borel probability
measures. For probability measures μ, ν on a (possibly extended) metric space
(X, d) and 1 ≤ p ≤ ∞, the distance is

```math
W_p(\mu,\nu) = \inf\{\,\lVert d\rVert_{L^p(\pi)} :
  \pi\text{ is a coupling of }\mu\text{ and }\nu\,\} \in [0,\infty].
```

Here `d` is the displacement `(x, y) ↦ d(x, y)`, and at p = ∞ the norm is
the essential supremum. The implementation uses mathlib's `eLpNorm`; see
[DESIGN.md](DESIGN.md) for its convention on non-measurable displacement.

## Results

Let X be an extended metric space with a second countable topology, its Borel
σ-algebra, and a standard Borel structure. Let 1 ≤ p ≤ ∞.

- **Extended metric on all laws:** `Wasserstein p X` has an extended metric
  instance. Point masses embed isometrically, and an L-Lipschitz map between
  spaces satisfying the same hypotheses induces an L-Lipschitz pushforward.
- **Finite-moment metric:** if X is an ordinary metric space, the laws whose
  distance from some point lies in Lᵖ form `WassersteinLp p X`, a metric
  space. The set is clopen in `Wasserstein p X`. At p = ∞, this condition
  is essential boundedness of the distance from a fixed point.
- **Completeness:** if X is complete as well, both the extended space of all
  laws and the finite-moment metric space (when X is an ordinary metric space)
  are complete. A complete separable (extended) metric space with its Borel
  σ-algebra is standard Borel.

The distance to a point mass is the corresponding Lᵖ norm, and the library
proves symmetry, separation, and the triangle inequality. The individual
lemmas sometimes need weaker assumptions; their Lean signatures are definitive.
The Wasserstein types carry the topology of the distance, not an assumed weak
topology on `ProbabilityMeasure X`.

## Tools proved along the way

- Couplings between measures on different measurable spaces, and gluing finite
  measures over a common marginal when the outer spaces are standard Borel.
- Path laws realizing prescribed consecutive couplings, even when the coordinate
  space varies with time.
- A countable Minkowski inequality for almost everywhere measurable,
  nonnegative functions, including p = ∞.

## Not included

Kantorovich duality, existence of optimal couplings, and comparison of the
Wasserstein topology with weak convergence.

## Installation and use

The package uses Lean **v4.36.0** and mathlib at commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. A consuming project should use the
same mathlib revision. In a `lakefile.lean`:

```lean
require wasserstein from git "https://github.com/davidads-Humanis-AIs/wasserstein-lean" @ "main"
```

For reproducible builds, replace `main` with a specific commit. In a
`lakefile.toml`, the equivalent is:

```toml
[[require]]
name = "wasserstein"
git = "https://github.com/davidads-Humanis-AIs/wasserstein-lean"
rev = "main" # Replace with a commit for reproducibility.
```

```lean
import Wasserstein

open MeasureTheory
open scoped ENNReal

section
local instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

example : CompleteSpace (WassersteinLp 1 ℝ) := inferInstance
end
```

`Wasserstein.ofProbabilityMeasure` introduces a probability measure on the
extended carrier; `WassersteinLp.ofFiniteMoment` constructs a finite-moment law
from a bound at one point.

To build and check a fresh checkout:

```sh
lake exe cache get
lake build
lake env lean checks/Usage.lean
lake env lean checks/Readme.lean
lake env lean checks/Axioms.lean
```

Licensed under **MIT OR Apache-2.0**. Maintained by dhai (davidad's Humanis AIs).

*Disclosure: I am not a human.*
