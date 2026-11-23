# Design and assumptions

## Conventions

The exponent is `p : ℝ≥0∞`, and metric results use `[Fact (1 ≤ p)]`, so
both finite exponents and `∞` are covered. Transport cost is mathlib's
`eLpNorm` of the displacement. For finite positive p, it is the p-th root of
the integral of the p-th power when displacement is almost everywhere
measurable for the plan; for p = ∞ it is the essential supremum. If
almost-everywhere strong measurability fails, `eLpNorm` is `∞`. A second
countable extended metric space with its Borel σ-algebra gives a measurable
displacement for every plan.

This convention matters for self-distance in arbitrary measurable spaces.
Take a two-point discrete metric space with the trivial σ-algebra. Its product
σ-algebra is also trivial, and the displacement, which takes both values 0 and
1, is not almost everywhere measurable under a probability plan. Its cost is
therefore `∞`; the unrestricted self-distance theorem would be false. The
library instead proves self-distance zero when the zero-displacement set is
measurable, and obtains the usual result from second countability and Borel
measurability.

`Wasserstein.map` requires a proof that the function is measurable. Mathlib's
probability-measure pushforward is totalized, so an unrestricted API can silently
produce the totalized value for a non-a.e.-measurable map. Requiring measurability
makes the public pushforward mean the usual pushforward; Lipschitz maps provide
this proof by continuity in the Borel setting.

## Headline hypotheses

| Result | Assumptions |
| --- | --- |
| Countable Minkowski | Countable index set; nonnegative functions almost everywhere measurable; `1 ≤ p ≤ ∞`. |
| Gluing | Two finite measures sharing their middle marginal; the outer measurable spaces are standard Borel. |
| Path law | Initial law is a probability measure; consecutive pair laws are finite couplings with matching marginals; successor spaces are nonempty and standard Borel. Coordinate spaces may vary. |
| Triangle inequality | Pseudo-extended metric space, second countable with opens measurable, standard Borel; first two laws finite; `1 ≤ p ≤ ∞`. |
| Extended metric instance on all laws | Extended metric space, second countable, Borel σ-algebra, standard Borel; `1 ≤ p ≤ ∞`. |
| Finite-moment metric and clopen set | Ordinary metric space, second countable, Borel σ-algebra, standard Borel; `1 ≤ p ≤ ∞`. |
| Completeness | Complete second countable extended metric space with its Borel σ-algebra, and `1 ≤ p ≤ ∞`; the finite-moment metric additionally requires an ordinary metric. Standard Borel is inferred. |
| Lipschitz pushforward | Both spaces satisfy the extended-metric instance assumptions, with the same exponent; the map is L-Lipschitz. |

The precise theorems sometimes require less: consult their Lean signatures.

## Construction

First the library equips all probability laws with an extended metric. On an
ordinary metric space, the finite-moment laws form the finite-distance component
of any point mass (when the space is nonempty). This component is clopen, hence
closed; completeness follows by restricting the complete extended space to it.
The empty case is handled separately. At p = ∞, finite moment means that the
distance to a fixed point is essentially bounded under the law.

## Not included

The library does not prove Kantorovich duality, existence of optimal couplings,
or comparison with weak convergence.

## Upstreaming

A possible PR sequence is countable Minkowski; couplings and gluing; path laws;
basic distance and Dirac formulas; triangle and metric instances; then
completeness. Review questions include a type synonym versus a one-field
structure, as with `WithLp`; the names `WassersteinLp` and `transportCost`;
whether `HasFiniteMoment` belongs on `Measure X`; and namespace choice. These
are prospective API decisions, not changes in this release.
