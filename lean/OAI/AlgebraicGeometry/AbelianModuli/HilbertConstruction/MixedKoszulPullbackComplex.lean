import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulStepPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulGeometricSupport

/-! # Mixed Koszul Pullback Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulPullbackComplex

noncomputable section

/-! The entire mixed Koszul complex, including its common zero set,
commutes with arbitrary scheme pullback. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}}

local instance mixedPullbackAdditive (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _
local instance mixedPullbackTensorAdditive {T : Scheme.{u}} (L : Line.Bundles.LineBundle T) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

theorem lineBundleSectionComplexMap_natural (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) {C D : CochainComplex X.Modules ℤ} (φ : C ⟶ D) :
    φ ≫ LineBundle.SectionKoszulStep.lineBundleSectionComplexMap L s D = LineBundle.SectionKoszulStep.lineBundleSectionComplexMap L s C ≫
      (((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.mapHomologicalComplex (.up ℤ)).map φ) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact LineBundle.SectionTensor.lineBundleSectionTensorMap_natural L s (φ.f i)

def lineBundleKoszulStepIsoOfComplexIso (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) {C D : CochainComplex X.Modules ℤ} (e : C ≅ D) :
    LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s C ≅ LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s D :=
  HomologicalComplex.homotopyCofiber.mapArrowIso
    (LineBundle.SectionKoszulStep.lineBundleSectionComplexMap L s C) (LineBundle.SectionKoszulStep.lineBundleSectionComplexMap L s D)
    (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
    (Arrow.isoMk e (((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.mapHomologicalComplex (.up ℤ)).mapIso e)
      (lineBundleSectionComplexMap_natural L s e.hom))

def pullbackLineBundleSection (f : Y ⟶ X) (b : LineBundleKoszulComplex.LineBundleSection X) : LineBundleKoszulComplex.LineBundleSection Y :=
  ⟨b.1.pullback f, Ample.LineBundles.pullbackSection f b.2⟩

def mixedKoszulPullbackIso (f : Y ⟶ X) (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs)) ≅
      LineBundleKoszulComplex.mixedLineBundleKoszulComplex ((Scheme.Modules.pullback f).obj M)
        (bs.map (pullbackLineBundleSection f)) := by
  let P := Scheme.Modules.pullback f
  induction bs with
  | nil => exact (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app M
  | cons b bs ih =>
    exact LineBundle.KoszulStepPullback.lineBundleKoszulStepPullbackIso f b.1 b.2 (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs) ≪≫
      lineBundleKoszulStepIsoOfComplexIso (b.1.pullback f) (Ample.LineBundles.pullbackSection f b.2) ih

theorem mixedSectionZeroSet_pullback (f : Y ⟶ X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    MixedKoszulGeometricSupport.mixedSectionZeroSet (bs.map (pullbackLineBundleSection f)) = f ⁻¹' MixedKoszulGeometricSupport.mixedSectionZeroSet bs := by
  ext y
  change (∀ b ∈ bs.map (pullbackLineBundleSection f), y ∉ Ample.LineBundles.sectionNonvanishing b.2) ↔ _
  rw [List.forall_mem_map]
  change (∀ b ∈ bs, y ∉ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f b.2)) ↔ _
  simp only [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulPullbackComplex
