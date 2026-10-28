import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterGeometricNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GeometricTransportCriterion

/-! # Universal Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The concrete full-level parameter has the expected universal level
for the original pullback operation on full ordered levels. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {g : ℕ} {S : Scheme.{u}} [IsNoetherian S] (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) [NeZero N]

theorem Abelian.Schemes.AbelianScheme.fullLevelParameterPointEquiv_natural {U T : Over S} (c : U ⟶ T)
    (y : T ⟶ A.fullLevelParameter N) :
    ((A.fullLevelParameterPointEquiv N T y).pullback c.left).transport
      (A.parameterPullbackIso c).symm = A.fullLevelParameterPointEquiv N U (c ≫ y) :=
  Abelian.Schemes.AbelianScheme.FullLevel.transport_parameterPullback_of_geometric A c
    (A.fullLevelParameterPointEquiv N T y) (A.fullLevelParameterPointEquiv N U (c ≫ y))
    (A.fullLevelParameterPointEquiv_geometric_natural N c y)

theorem Abelian.Schemes.AbelianScheme.universalFullLevel_point {T : Over S} (y : T ⟶ A.fullLevelParameter N) :
    ((A.universalFullLevel N).pullback y.left).transport (A.parameterPullbackIso y).symm =
      A.fullLevelParameterPointEquiv N T y :=
  Abelian.Schemes.AbelianScheme.FullLevel.transport_parameterPullback_of_geometric A y (A.universalFullLevel N)
    (A.fullLevelParameterPointEquiv N T y) (A.universalFullLevel_geometric_point N y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
