import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointFrameCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.ImageGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames

/-! # Adjoint Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointLift

noncomputable section

/-! Compatible frame images construct the map out of the pulled-back frame sheaf required by the pullback adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)
variable (hU : ∀ y : Y, ∃ i, y ∈ U i)
variable {N : X.Modules} (β : ModuleSheaf.openFrameModuleSheaf D ⟶ (Scheme.Modules.pushforward f).obj N)

def openFrameAdjointLift : ModuleSheaf.openFrameModuleSheaf (D.pullback f) ⟶ N :=
  (AdjointFrameCompatibility.adjointCompatibleFrameImages D f β).glue (ConstructedCompatibleFrames.openFrameSheafFrames (D.pullback f))
    (PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover f hU)

theorem openFrameAdjointLift_generator (V : X.Opens) (i : ι) (hi : V ≤ f ⁻¹ᵁ U i) (r : Γ(X, V)) :
    (openFrameAdjointLift D f hU β).app V (SectionGenerators.openFrameGenerator (D.pullback f) V i hi r) =
      r • AdjointFrameImages.adjointFrameImage D f β V i hi :=
  (AdjointFrameCompatibility.adjointCompatibleFrameImages D f β).glue_frame (ConstructedCompatibleFrames.openFrameSheafFrames (D.pullback f))
    (PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover f hU) V i hi r

theorem adjointFrameImage_preimage (W : Y.Opens) (i : ι) (hi : W ≤ U i) :
    AdjointFrameImages.adjointFrameImage D f β (f ⁻¹ᵁ W) i ((TopologicalSpace.Opens.map f.base).monotone hi) =
      β.app W (SectionGenerators.openFrameGenerator D W i hi 1) :=
  (AdjointFrameImages.adjointFrameImage_refine D f β (f ⁻¹ᵁ W) i ((TopologicalSpace.Opens.map f.base).monotone hi) W hi le_rfl).trans
    (ConcreteCategory.congr_hom (N.presheaf.map_id (.op (f ⁻¹ᵁ W))) _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointLift
