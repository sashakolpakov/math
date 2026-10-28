import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentationNaturality

/-! # Geometric Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricRefinement

noncomputable section

/-! Actual geometric frame arrows with a change of cover indices induce an
augmented map of the original sheafified free presentation resolutions. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  (T : C ⥤ D) {ι κ : Type v} (F : ι → C) (G : κ → D) (ρ : ι → κ)
  (α : ∀ i, T.obj (F i) ⟶ G (ρ i))

def presentationMap : CoveringPresentationPresheaf.presentations F ⟶
    T.op ⋙ CoveringPresentationPresheaf.presentations G where
  app _ := ↾fun x => ⟨⟨ρ x.down.1, T.map x.down.2 ≫ α x.down.1⟩⟩
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    refine Sigma.ext rfl ?_
    exact heq_of_eq ((congrArg (fun b => b ≫ α x.down.1) (T.map_comp f.unop x.down.2)).trans
      (Category.assoc _ _ _))

variable (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [T.IsContinuous J K] [T.IsCocontinuous J K]
  [∀ (M : Cᵒᵖ ⥤ ModuleCat.{max u v} R), T.op.HasPointwiseRightKanExtension M]

def map : CoveringPresentationResolution.complex J R F ⟶
    ((Cech.PresentationSheafRestriction.restriction R T J K).mapHomologicalComplex (.down ℕ)).obj
      (CoveringPresentationResolution.complex K R G) :=
  Cech.PresentationSheafRestriction.map R T J K (presentationMap T F G ρ α)

theorem augmentation_zero : (GeometricRefinement.map T F G ρ α R J K).f 0 ≫
    (Cech.PresentationSheafRestriction.restriction R T J K).map
      ((CoveringPresentationResolution.augmentation K R G).f 0) =
      (CoveringPresentationResolution.augmentation J R F).f 0 ≫
        (Cech.PresentationSheafRestriction.constantIso R T J K).inv :=
  Cech.PresentationSheafAugmentationNaturality.zero R T J K (presentationMap T F G ρ α)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricRefinement
