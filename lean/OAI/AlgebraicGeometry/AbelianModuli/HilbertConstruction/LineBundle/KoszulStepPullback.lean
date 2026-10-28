import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplicationPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulStep

/-! # Koszul Step Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulStepPullback

noncomputable section

/-! An actual line-bundle Koszul step commutes with arbitrary scheme
pullback, including its differential. The square follows from the
proved pullback formula for multiplication by the section. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}}

local instance koszulStepPullbackAdditive (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _
local instance koszulStepTensorAdditive {T : Scheme.{u}} (L : Line.Bundles.LineBundle T) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

theorem lineBundleSectionTensorMap_pullback (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (M : X.Modules) :
    (Scheme.Modules.pullback f).map (SectionTensor.lineBundleSectionTensorMap L s M) ≫
        (TensorPullbackFunctor.lineBundleTensorPullbackFunctorIso f L).hom.app M =
      SectionTensor.lineBundleSectionTensorMap (L.pullback f) (Ample.LineBundles.pullbackSection f s)
        ((Scheme.Modules.pullback f).obj M) := by
  let P := Scheme.Modules.pullback f
  have hs : SectionTensor.lineBundleSectionTensorMap L s M ≫ (TensorEquivalence.lineBundleTensorEquivalence_objIso L M).hom =
      Module.SectionMultiplication.moduleSectionMultiply L M s := by
    simp only [SectionTensor.lineBundleSectionTensorMap, Module.SectionMultiplication.moduleSectionMultiply, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hs' : SectionTensor.lineBundleSectionTensorMap (L.pullback f) (Ample.LineBundles.pullbackSection f s) (P.obj M) ≫
      (TensorEquivalence.lineBundleTensorEquivalence_objIso (L.pullback f) (P.obj M)).hom =
      Module.SectionMultiplication.moduleSectionMultiply (L.pullback f) (P.obj M) (Ample.LineBundles.pullbackSection f s) := by
    simp only [SectionTensor.lineBundleSectionTensorMap, Module.SectionMultiplication.moduleSectionMultiply, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (TensorEquivalence.lineBundleTensorEquivalence_objIso (L.pullback f) (P.obj M)).hom).mp
  change (P.map (SectionTensor.lineBundleSectionTensorMap L s M) ≫
      (P.map (TensorEquivalence.lineBundleTensorEquivalence_objIso L M).hom ≫ Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M ≫
        (TensorEquivalence.lineBundleTensorEquivalence_objIso (L.pullback f) (P.obj M)).inv)) ≫
      (TensorEquivalence.lineBundleTensorEquivalence_objIso (L.pullback f) (P.obj M)).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← P.map_comp, hs, hs']
  exact Module.SectionMultiplicationPullback.moduleSectionMultiply_pullback f L M s

def lineBundleTensorComplexPullbackIso (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (C : CochainComplex X.Modules ℤ) :
    (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj
      (((TensorEquivalence.lineBundleTensorEquivalence L).functor.mapHomologicalComplex (.up ℤ)).obj C)) ≅
    (((TensorEquivalence.lineBundleTensorEquivalence (L.pullback f)).functor.mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj C)) :=
  (NatIso.mapHomologicalComplex (TensorPullbackFunctor.lineBundleTensorPullbackFunctorIso f L) (.up ℤ)).app C

theorem lineBundleSectionComplexMap_pullback (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (C : CochainComplex X.Modules ℤ) :
    (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).map (SectionKoszulStep.lineBundleSectionComplexMap L s C)) ≫
        (lineBundleTensorComplexPullbackIso f L C).hom =
      SectionKoszulStep.lineBundleSectionComplexMap (L.pullback f) (Ample.LineBundles.pullbackSection f s)
        (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj C) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact lineBundleSectionTensorMap_pullback f L s (C.X i)

def lineBundleKoszulStepPullbackIso (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (C : CochainComplex X.Modules ℤ) :
    (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj (SectionKoszulStep.lineBundleSectionKoszulStep L s C)) ≅
      SectionKoszulStep.lineBundleSectionKoszulStep (L.pullback f) (Ample.LineBundles.pullbackSection f s)
        (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj C) := by
  let P := Scheme.Modules.pullback f
  let PC := (P.mapHomologicalComplex (.up ℤ)).obj C
  let a := (P.mapHomologicalComplex (.up ℤ)).map (SectionKoszulStep.lineBundleSectionComplexMap L s C)
  let b := SectionKoszulStep.lineBundleSectionComplexMap (L.pullback f) (Ample.LineBundles.pullbackSection f s) PC
  exact CochainComplex.mappingCone.mapHomologicalComplexIso (SectionKoszulStep.lineBundleSectionComplexMap L s C) P ≪≫
    HomologicalComplex.homotopyCofiber.mapArrowIso a b
      (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
      (Arrow.isoMk (Iso.refl PC) (lineBundleTensorComplexPullbackIso f L C) (by
        change 𝟙 PC ≫ b = a ≫ (lineBundleTensorComplexPullbackIso f L C).hom
        rw [Category.id_comp]
        exact (lineBundleSectionComplexMap_pullback f L s C).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulStepPullback
