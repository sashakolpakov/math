import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSheafMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality

/-! # Adjoint Frame Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointFrameImages

noncomputable section

/-! A map into a direct image supplies actual images of local frame generators on all subopens of the inverse-image cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U) (f : X ⟶ Y)
variable {N : X.Modules} (β : OpenFrame.ModuleSheaf.openFrameModuleSheaf D ⟶ (Scheme.Modules.pushforward f).obj N)

def adjointFrameImage (V : X.Opens) (i : ι) (hi : V ≤ f ⁻¹ᵁ U i) : Γ(N, V) :=
  N.presheaf.map (homOfLE hi).op (β.app (U i) (OpenFrame.SectionGenerators.openFrameGenerator D (U i) i le_rfl 1))

theorem adjointFrameImage_restrict (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : V ≤ f ⁻¹ᵁ U i) :
    N.presheaf.map (homOfLE h).op (adjointFrameImage D f β V i hi) =
      adjointFrameImage D f β W i (h.trans hi) :=
  (ConcreteCategory.congr_hom (N.presheaf.map_comp (homOfLE hi).op (homOfLE h).op)
    (β.app (U i) (OpenFrame.SectionGenerators.openFrameGenerator D (U i) i le_rfl 1))).symm

theorem adjointFrameImage_refine (V : X.Opens) (i : ι) (hi : V ≤ f ⁻¹ᵁ U i)
    (W : Y.Opens) (hW : W ≤ U i) (hV : V ≤ f ⁻¹ᵁ W) :
    adjointFrameImage D f β V i hi = N.presheaf.map (homOfLE hV).op
      (β.app W (OpenFrame.SectionGenerators.openFrameGenerator D W i hW 1)) := by
  have hg : (OpenFrame.ModuleSheaf.openFrameModuleSheaf D).presheaf.map (homOfLE hW).op
      (OpenFrame.SectionGenerators.openFrameGenerator D (U i) i le_rfl 1) = OpenFrame.SectionGenerators.openFrameGenerator D W i hW 1 :=
    (OpenFrame.GeneratorNaturality.openFrameGenerator_restriction D hW i le_rfl 1).trans
      (congrArg (OpenFrame.SectionGenerators.openFrameGenerator D W i hW) ((Y.presheaf.map (homOfLE hW).op).hom.map_one))
  have hb := ConcreteCategory.congr_hom (β.mapPresheaf.naturality (homOfLE hW).op)
    (OpenFrame.SectionGenerators.openFrameGenerator D (U i) i le_rfl 1)
  have he := (ConcreteCategory.congr_hom (N.presheaf.map_comp
    (homOfLE ((TopologicalSpace.Opens.map f.base).monotone hW)).op (homOfLE hV).op)
      (β.app (U i) (OpenFrame.SectionGenerators.openFrameGenerator D (U i) i le_rfl 1)))
  exact he.trans (congrArg (N.presheaf.map (homOfLE hV).op)
    (hb.symm.trans (congrArg (β.app W) hg)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointFrameImages
