module

public import BrenierMoment.Tails
public import BrenierMoment.MomentP4
public import BrenierMoment.MomentTail
public import BrenierMoment.BalanceP4
public import BrenierMoment.Threshold
public import BrenierMoment.OneSided
public import BrenierMoment.Clip
public import BrenierMoment.ClipSlack
public import BrenierMoment.FourCellGeometry
public import BrenierMoment.FourCellSlices
public import BrenierMoment.FourAtomTargets
public import BrenierMoment.CoordBox
public import BrenierMoment.FourAtomSharp
public import BrenierMoment.SharpRate
public import BrenierMoment.Sharpness
public import BrenierMoment.LastCoordinate
public import BrenierMoment.PotentialBound
public import BrenierMoment.PotentialBoundLimit
public import BrenierMoment.PowerSource
public import BrenierMoment.LogConcave
public import BrenierMoment.LineInterpolation
public import BrenierMoment.CoordSlices
public import BrenierMoment.SourceInterpolation
public import BrenierMoment.StripInterpolation
public import BrenierMoment.ActiveMaps
public import BrenierMoment.PlanComparison
public import BrenierMoment.LimitCertificate
public import BrenierMoment.FiniteTargets
public import BrenierMoment.GeneralTargets
public import BrenierMoment.MomentStability
public import BrenierMoment.UniformBase
public import BrenierMoment.UpperBound
public import BrenierMoment.TwoSided
public import BrenierMoment.Presentation.Model
public import BrenierMoment.FCPresentation

public section

/-!
# Brenier moment stability

The upper bound is `BrenierMoment.moment_stability`: for a source with density
proportional to `exp (-V)` on a bounded open convex set, with `V` convex, a
target with power-logarithmic moment at most one and a target with finite
second moment have unique optimal maps, and the maps differ in `L²` of the
source by at most a constant times
`δ ^ ((p - 2) / (3p - 2)) * log (e / δ) ^ (-2β / (3p - 2))`, `δ = W₂`.

Sharpness is `BrenierMoment.moment_rate_sharp` and
`BrenierMoment.no_modulus_at_second_moment`. On the box source of the sharpness
statements both bounds hold for the same pairs of targets:
`BrenierMoment.moment_rate_two_sided`.

The same three statements with definitions that use Mathlib alone are
`BrenierStability.moment_stability`, `BrenierStability.moment_rate_sharp` and
`BrenierStability.no_modulus_at_second_moment` in `FCPresentation.lean`.
-/
