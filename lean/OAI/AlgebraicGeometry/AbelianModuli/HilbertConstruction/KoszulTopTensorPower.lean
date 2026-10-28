import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroTensorPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SectionCokernelCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeTopTerm
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteModuleTensorAssociativity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Koszul Top Tensor Power -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulTopTensorPower

noncomputable section

/-! The zero-degree term of the actual section Koszul complex is the
coefficient sheaf tensored by one defining line-bundle factor per section. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

def lineBundleKoszulTopTermIso (L : Line.Bundles.LineBundle X) (M : X.Modules) :
    (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) →
      (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X 0 ≅ Tensor.ProductSheaf.tensorModule (L.tensorPower ss.length).sheaf M
  | [] => (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).symm ≪≫
      Tensor.Bifunctor.tensorModuleMapIso L.tensorPowerZeroIso.symm (Iso.refl M)
  | s :: ss =>
      let K := LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss
      let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor
      MappingConeTopTerm.mappingConeTopProjectionIso (LineBundle.SectionKoszulStep.lineBundleSectionComplexMap L s K)
          (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss 1 (Or.inr (by decide))) ≪≫
        F.mapIso (lineBundleKoszulTopTermIso L M ss) ≪≫
        LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso L (Tensor.ProductSheaf.tensorModule (L.tensorPower ss.length).sheaf M) ≪≫
        (ConcreteModuleTensorAssociativity.actualModuleTensorAssoc L.sheaf (L.tensorPower ss.length).sheaf M).symm ≪≫
        Tensor.Bifunctor.tensorModuleMapIso (L.tensor_succ_sheafIso ss.length).some (Iso.refl M)

def lineBundleSquareKoszulTopPowerIso (G : Line.Bundles.LineBundle X)
    (ss : List (Line.Bundles.structureModule X ⟶ (G.tensorPower 2).sheaf)) (b : ℕ) :
    (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex (G.tensorPower 2) (G.tensorPower b).sheaf ss).X 0 ≅
      (G.tensorPower (ss.length * 2 + b)).sheaf :=
  KoszulTopTensorPower.lineBundleKoszulTopTermIso (G.tensorPower 2) (G.tensorPower b).sheaf ss ≪≫
    Tensor.Bifunctor.tensorModuleMapIso (G.tensorPowerComposeIso ss.length 2).symm (Iso.refl _) ≪≫
      (G.tensorPowerAddIso (ss.length * 2) b).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulTopTensorPower
