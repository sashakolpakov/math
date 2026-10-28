import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.QuotientProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CoordinatePullback

/-! # Quotient Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientReduction.IntegralCechQuotientReduction

noncomputable section

/-! Native reduction in the original integral Cech total agrees
with pointwise quotient reduction and preserves geometric pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (I : Ideal R)

def presheafMap (Z : Over (Spec (CommRingCat.of R))) :=
  CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.complex R I (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z))

def bicomplexMap (Z : Over (Spec (CommRingCat.of R))) {ν : Type} (W : ν → Z.left.Opens) :=
  CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.bicomplex R I (FormalCoproduct.mk ν W).cech
    (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z))

def map (Z : Over (Spec (CommRingCat.of R))) {ν : Type} (W : ν → Z.left.Opens) :=
  CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.map R I (FormalCoproduct.mk ν W).cech
    (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z))

theorem coordinates (Z : Over (Spec (CommRingCat.of R))) {ν : Type} [Finite ν] (W : ν → Z.left.Opens) :
    IntegralComparison.Module.IdealQuotient.complexProjection R I
      ((IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R Z W).total (.up ℕ)) ≫
        (QuotientTotal.IntegralCechQuotientTotal.iso R Z W I).hom = IntegralCechQuotientReduction.map R I Z W :=
  CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.total R I (FormalCoproduct.mk ν W).cech
    (QuotientTotal.IntegralCechQuotientTotal.finiteIndices R Z W)
    (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z))

variable {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

theorem presheaf_square : presheafMap R I Y ≫ Integral.QuotientCechPullback.IntegralQuotientCechPullback.presheafMap R f I =
    IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap f ≫
      ((Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)).map (presheafMap R I X) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext W
  exact ((IntegralComparison.Module.IdealQuotient.projection R I).naturality
    (((IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap f).f q).app W)).symm

variable {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

theorem bicomplex_naturality : bicomplexMap R I Y U ≫ Integral.QuotientCechPullback.IntegralQuotientCechPullback.bicomplexMap R f I U V r hr =
    CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R f U V r hr ≫ bicomplexMap R I X V :=
  Cech.ComplexPullback.CechPullback.bicomplex_naturality R f.left U V r hr
    (IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap f) (Integral.QuotientCechPullback.IntegralQuotientCechPullback.presheafMap R f I)
    (presheafMap R I Y) (presheafMap R I X) (presheaf_square R I f).symm

theorem naturality : IntegralCechQuotientReduction.map R I Y U ≫ Integral.QuotientCechPullback.IntegralQuotientCechPullback.map R f I U V r hr =
    HomologicalComplex₂.total.map (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R f U V r hr) (.up ℕ) ≫
      IntegralCechQuotientReduction.map R I X V :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
    ((congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex_naturality R I f U V r hr)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientReduction.IntegralCechQuotientReduction
