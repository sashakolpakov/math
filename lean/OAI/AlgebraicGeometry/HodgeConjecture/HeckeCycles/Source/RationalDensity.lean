import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionClosure
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RotatedActiveDensity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductCompatibility

/-! # Rational Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalDensity

noncomputable section

/-! Density of the actual rational source in its active SL3 factor and
commuting away range, with the topology of the other finite places. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

namespace CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization

private theorem subgroupClosure {X A B Γ : Type*}
    [Group X] [Group A] [Group B] [Group Γ]
    [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalGroup X] [IsTopologicalGroup A]
    (p : A →* B) (r : Γ →* X × A) (s : Γ →* X × B)
    (hc : ∀ g, Prod.map id p (r g) = s g) (hp : Topology.IsInducing p)
    (x : X) (hx : (x, (1 : B)) ∈ closure (Set.range s)) :
    (x, (1 : A)) ∈ r.range.topologicalClosure :=
  CMExtraction.InducedProductCompatibility.Approximation.compatible_induced_supported_closure p r s hc hp x hx

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance awayGroup : Group (FactorTheta.CM.RationalWeilFactorization.Away E L f) := Subgroup.toGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f)
local instance awayMulOneClass : MulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  SubmonoidClass.toMulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f)
local instance sourceMulOneClass :
    MulOneClass (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (show Group (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) from Prod.instGroup).toMulOneClass
local instance awayTopologicalGroup : IsTopologicalGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  RationalAwayTopology.CM.topologicalGroup E L f

local instance sourceTopologicalGroup :
    IsTopologicalGroup (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  Prod.instIsTopologicalGroup

abbrev binary_mem_closure (A : Matrix.SpecialLinearGroup (Fin 2) ℚ_[q]) :=
  subgroupClosure (RationalAwayTopology.CM.coordinates E L f) (RationalAwayTopology.CM.rational E L f)
    (SourceAdelic.Projection.CM.rational E (OppositeCoordinates.CM.coordinates E L.coordinates) f)
    (RationalAwayTopology.CM.compatible E L f) (RationalAwayTopology.CM.coordinates_inducing E L f) (CMExtraction.Quaternion.QuadraticUnitary.activeBinaryBlock A)
    (QuaternionClosure.CM.binary_mem_closure_restricted E
      (OppositeCoordinates.CM.coordinates E L.coordinates) f A)

theorem dense : DenseRange (RationalAwayTopology.CM.rational E L f) := by
  let γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b :=
    CMExtraction.ActiveRotation.Approximation.positiveRotationUnitary E (NumberField.IsCMField.complexConj E).toRingHom B.b
  have hγ : (RationalAwayTopology.CM.rational E L f γ).1 = CMExtraction.ActiveRotation.Approximation.positiveRotation ℚ_[q] := CMExtraction.ActiveRotation.Approximation.positiveRotation_map E f
  apply CMExtraction.RotatedActiveDensity.Approximation.denseRange_product_of_binary_and_rotation (RationalAwayTopology.CM.rational E L f) (RationalAwayTopology.CM.away_surjective E L f) γ hγ
  · intro x
    simpa only [CMExtraction.ActiveRotation.Approximation.activeBinaryBlock_forward] using
      binary_mem_closure E L f (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) x)
  · intro x
    simpa only [CMExtraction.ActiveRotation.Approximation.activeBinaryBlock_backward] using
      binary_mem_closure E L f (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) x)

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalDensity
