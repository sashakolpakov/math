import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePullback

/-! # Quotient Cech Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechPullback.IntegralQuotientCechPullback

noncomputable section

/-! The original geometric quotient Cech pullback commutes with
projection from the full de Rham complex to its first three terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (I : Ideal R)

def truncated (Z : Over (Spec (CommRingCat.of R))) :=
  ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.presheaves R Z I).mapHomologicalComplex (.up ℕ)).obj
    (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z))

def projection (Z : Over (Spec (CommRingCat.of R))) : OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R Z I ⟶
    truncated R I Z :=
  ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.presheaves R Z I).mapHomologicalComplex (.up ℕ)).map
    (FirstThree.ThreeComplex.FirstThreeComplex.projection (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z))

def presheafMap : truncated R I Y ⟶
    ((Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)).obj (truncated R I X) :=
  ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.presheaves R Y I).mapHomologicalComplex (.up ℕ)).map
    (IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap f)

theorem presheaf_square : projection R I Y ≫ presheafMap R f I =
    Affine.PairQuotientPullback.AffinePairQuotientPullback.originalMap R f I ≫
      ((Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)).map (projection R I X) := by
  let Q := (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.presheaves R Y I).mapHomologicalComplex (.up ℕ)
  exact (Q.map_comp _ _).symm.trans
    ((congrArg Q.map (FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_projection
      (DeRham.Int.directImagePresheaf f) (DeRham.Int.presheafPullback f))).trans (Q.map_comp _ _))

variable {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

def bicomplexMap : IntegralCech.QuotientTotal.IntegralCechQuotientTotal.bicomplex R Y U I ⟶
    IntegralCech.QuotientTotal.IntegralCechQuotientTotal.bicomplex R X V I :=
  Cech.ComplexPullback.CechPullback.bicomplexMap R f.left U V r hr (presheafMap R f I)

def fullBicomplexMap : IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R Y U I ⟶
    IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X V I :=
  Cech.ComplexPullback.CechPullback.bicomplexMap R f.left U V r hr (Affine.PairQuotientPullback.AffinePairQuotientPullback.originalMap R f I)

theorem bicomplex_square :
    FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap R (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.rows R Y U I)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) ≫ bicomplexMap R f I U V r hr =
    fullBicomplexMap R f I U V r hr ≫
      FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap R (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.rows R X V I)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  Cech.ComplexPullback.CechPullback.bicomplex_naturality R f.left U V r hr
    (Affine.PairQuotientPullback.AffinePairQuotientPullback.originalMap R f I) (presheafMap R f I)
    (projection R I Y) (projection R I X) (presheaf_square R f I).symm

def map := HomologicalComplex₂.total.map (bicomplexMap R f I U V r hr) (.up ℕ)
def fullMap := HomologicalComplex₂.total.map (fullBicomplexMap R f I U V r hr) (.up ℕ)

theorem total_square : IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection R Y U I ≫ IntegralQuotientCechPullback.map R f I U V r hr =
    fullMap R f I U V r hr ≫ IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection R X V I :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
    ((congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex_square R f I U V r hr)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

theorem homology : HomologicalComplex.homologyMap (fullMap R f I U V r hr) 1 ≫
    (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X V I).hom =
      (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R Y U I).hom ≫
        HomologicalComplex.homologyMap (IntegralQuotientCechPullback.map R f I U V r hr) 1 :=
  (HomologicalComplex.homologyMap_comp _ _ 1).symm.trans
    ((congrArg (fun a => HomologicalComplex.homologyMap a 1) (total_square R f I U V r hr).symm).trans
      (HomologicalComplex.homologyMap_comp _ _ 1))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechPullback.IntegralQuotientCechPullback
