module

public import HolderToCK.Foundation.HolderBounds
public import HolderToCK.Foundation.WeakPoisson
public import HolderToCK.Foundation.DerivativeBounds
public import HolderToCK.Integration.HolderInput
public import HolderToCK.Analysis.MollificationForcingBound
public import HolderToCK.Analysis.ClassicalWeakGradient
public import HolderToCK.Foundation.HolderContinuity
public import HolderToCK.Analysis.HolderMollification
public import HolderToCK.Analysis.ZeroBoundaryClosure
public import HolderToCK.Analysis.ClassicalEquation
public import HolderToCK.Analysis.Harmonic.EnergyDecay
public import HolderToCK.Analysis.Harmonic.DerivativeFields
public import HolderToCK.Analysis.Harmonic.WeakEnergyOrthogonality
public import HolderToCK.Analysis.Harmonic.WeakGradientError
public import HolderToCK.Analysis.Bootstrap.ForcingRepresentative
public import HolderToCK.Analysis.SegmentDerivativeIdentity
public import HolderToCK.Analysis.Bootstrap.WeakDifferentiation
public import HolderToCK.Analysis.Bootstrap.CoefficientBounds
public import HolderToCK.Analysis.Bootstrap.QuadraticForcingBounds
public import HolderToCK.Analysis.Bootstrap.FirstDerivativeHolder
public import HolderToCK.Analysis.Poisson.RadialHessian
public import HolderToCK.Analysis.Harmonic.GradientExcess
public import HolderToCK.Analysis.Poisson.KernelCancellation
public import HolderToCK.Analysis.Poisson.WeakHarmonicSmooth
public import HolderToCK.Analysis.Bootstrap.CoordinateWords
public import HolderToCK.Analysis.Bootstrap.AffineDerivatives
public import HolderToCK.Analysis.Bootstrap.QuadraticComposition
public import HolderToCK.Geometry.MinimizerRepresentativeEquation
public import HolderToCK.Analysis.Harmonic.EnergyExcessComparison
public import HolderToCK.Analysis.Poisson.DistributionIdentity
public import HolderToCK.Analysis.Poisson.ForcingCutoff
public import HolderToCK.Analysis.Harmonic.HigherHolderEstimates

public import HolderToCK.Analysis.QuadraticPoissonC1
public import HolderToCK.Analysis.LocalQuadraticPoissonC1
public import HolderToCK.Analysis.Poisson.PotentialRegularityBounds
public import HolderToCK.Analysis.Poisson.InteriorPoissonRegularity
public import HolderToCK.Analysis.Poisson.ForcingLocalization
public import HolderToCK.Analysis.Harmonic.UnitC2Bounds

/-! # Holder-to-smooth regularity library

The library exposes literal estimate and equation definitions, signed weak
Poisson mollification and its local forcing estimates, native local Sobolev
data of C1 maps, harmonic energy and derivative fields, native zero-boundary
closure and Green identities, classical forcing representatives, and pinned inputs.
Finite weak differentiation, compact coefficient bounds, quadratic forcing
estimates, harmonic derivative and gradient-excess bounds, continuous Sobolev
replacement and quadratic error, all-order forcing bounds, normalized
fundamental kernels and their distributional Laplacian, annular cancellation,
continuous weak harmonic smoothness, and same-representative projection
equations are also exposed.
The quantitative C1 statement is sealed, source audited and ABI verified.
The quantitative Schauder, qualitative smoothness and all-order small-energy
statements are proved. The source-facing exports are available through
`HolderToCK.Regularity`. The mathematical arguments are documented in the
public manuscripts, and the verification tools check their complete interfaces
and source fingerprints. This analytic facade stays below those exports in
the import DAG.
-/

public section
