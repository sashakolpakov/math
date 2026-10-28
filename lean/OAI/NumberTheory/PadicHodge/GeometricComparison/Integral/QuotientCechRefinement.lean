import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientReduction
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinementCoefficient

/-! # Quotient Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechRefinement.IntegralQuotientCechRefinement

noncomputable section

/-! Actual source-cover refinement preserves both the original
full-to-three-term quotient comparison and integral reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (I : Ideal R)
  {ι κ : Type} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X
local notation "K₃" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex K

def rows : IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.rows R X U I ⟶ IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.rows R X V I :=
  Functor.whiskerLeft (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.presheaves R X I) (NonemptyCech.Refinement.NonemptyCechRefinement.transformation U V r)

def fullMap := CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map U V r (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I)
def map := CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map U V r (QuotientCechPullback.IntegralQuotientCechPullback.truncated R I X)

theorem projection : IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection R X U I ≫ IntegralQuotientCechRefinement.map R X I U V r =
    fullMap R X I U V r ≫ IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection R X V I :=
  FirstThree.MappedTotalNaturality.FirstThreeMappedTotalNaturality.natural R (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.rows R X U I)
    (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.rows R X V I) (rows R X I U V r) K

theorem homology : HomologicalComplex.homologyMap (fullMap R X I U V r) 1 ≫
    (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X V I).hom =
      (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X U I).hom ≫
        HomologicalComplex.homologyMap (IntegralQuotientCechRefinement.map R X I U V r) 1 :=
  (HomologicalComplex.homologyMap_comp _ _ 1).symm.trans
    ((congrArg (fun a => HomologicalComplex.homologyMap a 1) (projection R X I U V r).symm).trans
      (HomologicalComplex.homologyMap_comp _ _ 1))

theorem bicomplex_reduction : IntegralCech.QuotientReduction.IntegralCechQuotientReduction.bicomplexMap R I X U ≫
    CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap U V r (QuotientCechPullback.IntegralQuotientCechPullback.truncated R I X) =
      CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap U V r K₃ ≫
        IntegralCech.QuotientReduction.IntegralCechQuotientReduction.bicomplexMap R I X V :=
  ((NonemptyCech.Refinement.NonemptyCechRefinement.transformation U V r).mapHomologicalComplex (.up ℕ)).naturality
    (IntegralCech.QuotientReduction.IntegralCechQuotientReduction.presheafMap R I X)

theorem reduction : IntegralCech.QuotientReduction.IntegralCechQuotientReduction.map R I X U ≫ IntegralQuotientCechRefinement.map R X I U V r =
    CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map U V r K₃ ≫ IntegralCech.QuotientReduction.IntegralCechQuotientReduction.map R I X V :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
    ((congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex_reduction R X I U V r)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechRefinement.IntegralQuotientCechRefinement
