import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SectionIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

/-! # Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SourceCoordinates

noncomputable section

/-! The genuine source-resolution augmentation evaluates a global
section at one on each covering-frame intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R]
  (J : GrothendieckTopology C) (H : Sheaf J (ModuleCat.{max u v} R))
  (b : (constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R) ⟶ H)

local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation J R F

omit [HasBinaryProducts C] in
theorem unadjoint :
    Presentation.ResolutionCoordinates.unadjoint F R 0 J H ((ε).f 0 ≫ b) =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R
        (CoveringPresentationPresheaf.presentations F)).f 0 ≫
          Ext.ZeroPresheafSections.homLinearEquiv R J H b := by
  dsimp only [Presentation.ResolutionCoordinates.unadjoint,
    CoveringPresentationResolution.augmentation]
  rw [Cech.PresentationSheafAugmentation.zero]
  exact (sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv_naturality_left _ _

theorem coordinate (t : Fin 1 → ι) :
    Presentation.ResolutionCoordinates.sheaf F R 0 J H ((ε).f 0 ≫ b) t =
      (Ext.ZeroPresheafSections.homLinearEquiv R J H b).app
        (op (Presentation.TupleProducts.family F 0 t)) (1 : R) := by
  rw [Presentation.ResolutionCoordinates.sheaf_apply, unadjoint]
  change (Ext.ZeroPresheafSections.homLinearEquiv R J H b).app
    (op (Presentation.TupleProducts.family F 0 t))
    (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R
      (CoveringPresentationPresheaf.presentations F)).f 0).app _
        (ModuleCat.freeMk (Presentation.ResolutionCoordinates.universalTuple F 0 t))) = _
  rw [Cech.PresentationMap.augmentation_generator]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SourceCoordinates
