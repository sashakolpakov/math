import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FrameTensorNaturalIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulStep

/-! # Line Bundle Koszul Step -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.LineBundleKoszulStep

noncomputable section

/-! In a global frame, an actual line-bundle Koszul step is isomorphic
as a complex to the cone of multiplication by its coordinate. The
comparison includes the differential and not only the individual terms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

local instance framedKoszulTensorAdditive (L : Line.Bundles.LineBundle X) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

def globalScalarComplexMap (r : Γ(X, ⊤)) (C : CochainComplex X.Modules ℤ) : C ⟶ C where
  f i := Global.ModuleScalars.globalModuleScalar (C.X i) r
  comm' i j _ := Global.ModuleScalars.globalModuleScalar_natural r (C.d i j)

def lineBundleFrameComplexIso (L : Line.Bundles.LineBundle X) (e : L.sheaf ≅ Line.Bundles.structureModule X)
    (C : CochainComplex X.Modules ℤ) :
    (((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.mapHomologicalComplex (.up ℤ)).obj C) ≅ C :=
  (NatIso.mapHomologicalComplex (LineBundle.FrameTensorNaturalIso.lineBundleFrameTensorIso L e) (.up ℤ)).app C

theorem lineBundleSectionComplexMap_frame (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (e : L.sheaf ≅ Line.Bundles.structureModule X)
    (C : CochainComplex X.Modules ℤ) :
    LineBundle.SectionKoszulStep.lineBundleSectionComplexMap L s C ≫ (lineBundleFrameComplexIso L e C).hom =
      globalScalarComplexMap (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom)) C := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact LineBundle.FrameTensorNaturalIso.lineBundleSectionTensorMap_frame L s e (C.X i)

def framedLineBundleKoszulStepIso (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (e : L.sheaf ≅ Line.Bundles.structureModule X)
    (C : CochainComplex X.Modules ℤ) :
    LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s C ≅
      CochainComplex.mappingCone (globalScalarComplexMap (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom)) C) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso
    (LineBundle.SectionKoszulStep.lineBundleSectionComplexMap L s C)
    (globalScalarComplexMap (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom)) C)
    (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
    (Arrow.isoMk (Iso.refl C) (lineBundleFrameComplexIso L e C) (by
      exact (Category.id_comp _).trans (lineBundleSectionComplexMap_frame L s e C).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.LineBundleKoszulStep
