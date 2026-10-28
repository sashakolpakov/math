import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalDensity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DenseHomClosure

/-! # Intrinsic Active Closure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveClosure

noncomputable section

/-! The actual supported active SL3 subgroup lies in the closure of the
actual rational unitary subgroup inside the full finite unitary group. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization

namespace CM.Intrinsic

private def assembleHom {X A B G : Type*} [Group X] [Group A] [Group B] [Group G]
    (e : X × B ≃* G) (p : A →* B) :=
  e.toMonoidHom.comp ((MonoidHom.id X).prodMap p)

private theorem comp_eq_of_values {G H K : Type*} [Group G] [Group H] [Group K]
    (a : G →* H) (b : H →* K) (c : G →* K)
    (h : ∀ x, b (a x) = c x) : b.comp a = c :=
  MonoidHom.ext h

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

def assemble := assembleHom
  (SourceFinite.Product.CM.equivalence E (OppositeCoordinates.CM.coordinates E L.coordinates) f)
  (RationalAwayTopology.CM.nativeCoordinates E L f)

theorem continuous : Continuous (assemble E L f) :=
  (SourceFinite.Topology.CM.equivalence_continuous E
    (OppositeCoordinates.CM.coordinates E L.coordinates) f).comp
      (continuous_id.prodMap (RationalAwayCoordinates.CM.native_continuous E L f))

theorem rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    assemble E L f (RationalAwayTopology.CM.rational E L f g) =
      RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g :=
  SourceFinite.Product.CM.rational_factorization E
    (OppositeCoordinates.CM.coordinates E L.coordinates) f g

theorem active (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    assemble E L f (u, 1) = ActiveMetaplectic.CM.inclusion E L.coordinates f u := by
  exact congrArg (fun b : SourceFinite.Product.CM.Away E
    (OppositeCoordinates.CM.coordinates E L.coordinates) f =>
      SourceFinite.Product.CM.equivalence E (OppositeCoordinates.CM.coordinates E L.coordinates) f (u, b))
    (RationalAwayTopology.CM.nativeCoordinates E L f).map_one

private abbrev homProof := comp_eq_of_values
  (RationalAwayTopology.CM.rational E L f) (assemble E L f)
  (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates))
  (rational E L f)

theorem hom : type_of% (homProof E L f) := homProof E L f

theorem image_mem_closure (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    assemble E L f a ∈
      (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates)).range.topologicalClosure := by
  let := SourceFinite.Topology.CM.levels_open E (OppositeCoordinates.CM.coordinates E L.coordinates)
  exact DenseHomClosure.CM.mem
    (RationalAwayTopology.CM.rational E L f) (RationalDensity.CM.dense E L f)
    (assemble E L f) (continuous E L f)
    (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (rational E L f) a (assemble E L f a) rfl

end CM.Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveClosure
