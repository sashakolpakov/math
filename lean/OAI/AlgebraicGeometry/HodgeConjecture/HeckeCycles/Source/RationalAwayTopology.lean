import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Projection

/-! # Rational Away Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology

noncomputable section

/-! The actual commuting rational away range carries the topology
induced by its complementary finite-place coordinates. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

namespace CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization

private def subgroupFirstCoordinate {A B : Type*} [Group A] [Group B]
    (H : Subgroup (A × B)) : H →* A where
  toFun g := g.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

private def pairedCoordinates {G A M B : Type*} [Group G] [Group A] [Group M] [Group B]
    (a : G →* A) (active : A →* M) (rho : G →* M)
    (hc : ∀ g u, Commute (CommutingFactorization.CM.remainder a active rho g) (active u))
    (b : G →* B) :=
  a.prod (CommutingFactorization.CM.awayWithCoordinates a active rho hc b)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance awayGroup : Group (FactorTheta.CM.RationalWeilFactorization.Away E L f) := Subgroup.toGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f)
local instance awayMulOneClass : MulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (awayGroup E L f).toMulOneClass

def nativeCoordinates := subgroupFirstCoordinate (FactorTheta.CM.RationalWeilFactorization.Away E L f)

def coordinates :=
  (RestrictedAwayComparison.CM.forget
    (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (QadicPlace.CM.place E f)).comp (nativeCoordinates E L f)

instance topology : TopologicalSpace (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  TopologicalSpace.induced (CM.coordinates E L f) inferInstance

instance topologicalGroup : IsTopologicalGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f) := by
  let : IsTopologicalGroup (CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway
      (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (QadicPlace.CM.place E f)) :=
    RestrictedAwayComparison.CM.away_topologicalGroup
      (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (QadicPlace.CM.place E f)
  exact isTopologicalGroup_induced (CM.coordinates E L f)

theorem coordinates_inducing : Topology.IsInducing (CM.coordinates E L f) := ⟨rfl⟩

theorem coordinates_continuous : Continuous (CM.coordinates E L f) :=
  (coordinates_inducing E L f).continuous

def rational := pairedCoordinates
  (RationalFactorProjection.CM.activeLocal E f)
  (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f)
  (WeilData.CM.finiteHom E L) (FactorTheta.CM.RationalWeilFactorization.remainder_commutes E L f)
  (SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f)

theorem away_surjective : Function.Surjective (FactorTheta.CM.RationalWeilFactorization.away E L f) := by
  rintro ⟨g, ⟨γ, hγ⟩⟩
  exact ⟨γ, Subtype.ext hγ⟩

theorem compatible (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    Prod.map id (CM.coordinates E L f) (rational E L f g) =
      SourceAdelic.Projection.CM.rational E (OppositeCoordinates.CM.coordinates E L.coordinates) f g := by
  apply Prod.ext
  · exact (SourceAdelic.Projection.CM.rational_first E
      (OppositeCoordinates.CM.coordinates E L.coordinates) f g).symm
  · exact (SourceAdelic.Projection.CM.rational_away E
      (OppositeCoordinates.CM.coordinates E L.coordinates) f g).symm

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology
