import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELLevel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocal
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalOpen

/-! # Marked Away Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MarkedAwayLevel

noncomputable section

/-! Pull back the actual marked principal PEL level to the source away
group, retaining the rational-membership and assembly identifications. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology.CM

namespace CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance markedAwayGroup : Group (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  Subgroup.toGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f)

local instance markedAwayMonoid : Monoid (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (markedAwayGroup E L f).toMonoid

local instance markedAwayMulOneClass : MulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (markedAwayGroup E L f).toMulOneClass

def map : FactorTheta.CM.RationalWeilFactorization.Away E L f →ₜ* P.FiniteSpecialUnitary where
  toFun a := PELFiniteGroup.CM.pel E
    (OppositeCoordinates.CM.coordinates E L.coordinates) P hb a.val.1.val
  map_one' := (PELFiniteGroup.CM.pel E
    (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).map_one
  map_mul' a b := (PELFiniteGroup.CM.pel E
    (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).map_mul a.val.1.val b.val.1.val
  continuous_toFun := by
    have hs : Continuous (fun a : SourceFinite.Product.CM.Away E
        (OppositeCoordinates.CM.coordinates E L.coordinates) f =>
        (a.val : SourceFinite.Product.CM.FiniteGroup E
          (OppositeCoordinates.CM.coordinates E L.coordinates))) := continuous_subtype_val
    exact (PELFiniteGroup.CM.pel E
      (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).continuous.comp
        (hs.comp (RationalAwayCoordinates.CM.native_continuous E L f))

variable {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ P.lattice]
  (b : Module.Basis J ℤ P.lattice) (N : ℕ) (hN : 0 < N)

def level : OpenSubgroup (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (CMExtraction.PEL.PrincipalOpen.Approximation.pelPrincipalOpenSubgroup E P b N hN).comap
    (map E L P hb f).toMonoidHom (map E L P hb f).continuous

theorem rational_mem (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    FactorTheta.CM.RationalWeilFactorization.away E L f g ∈ level E L P hb f b N hN ↔
      FilledLocal.CM.PEL.hom E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb f g ∈
        P.adelicPrincipalLevel N := Iff.rfl

theorem assemble_away (a : FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (1, a) = (RationalAwayTopology.CM.nativeCoordinates E L f a).val := by
  have h := SourceFinite.Product.CM.equivalence_apply E
    (OppositeCoordinates.CM.coordinates E L.coordinates) f 1 (RationalAwayTopology.CM.nativeCoordinates E L f a)
  refine h.trans ?_
  have hi := congrArg (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
    (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (QadicPlace.CM.place E f))
    (QadicSpecialLinear.CM.equivalence E
      (OppositeCoordinates.CM.coordinates E L.coordinates) f).symm.map_one
  have hi' := hi.trans (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
    (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (QadicPlace.CM.place E f)).map_one
  exact (congrArg (fun g => g * (RationalAwayTopology.CM.nativeCoordinates E L f a).val) hi').trans (one_mul _)

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MarkedAwayLevel
