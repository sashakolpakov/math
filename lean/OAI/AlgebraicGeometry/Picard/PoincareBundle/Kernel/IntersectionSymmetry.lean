import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelTrivialization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareRecoveryFormula

/-! # Intersection Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionSymmetry

noncomputable section

/-! The actual symmetry on a subgroup intersection and the canonical exchanged kernel frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

theorem reverse_path {C : Type*} [Category C] {A B D E F G H : C}
    (a : B ≅ A) (b : B ≅ D) (c : D ≅ E) (d : F ≅ E) (e : G ≅ F) (f : G ≅ H) :
    (a.symm ≪≫ b ≪≫ c ≪≫ d.symm ≪≫ e.symm ≪≫ f).symm =
      f.symm ≪≫ e ≪≫ d ≪≫ c.symm ≪≫ b.symm ≪≫ a := by
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]

theorem regroup_path {C : Type*} [Category C] {A B D E F G H : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : E ≅ F) (e : F ≅ G) (f : G ≅ H) :
    a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ f = ((a ≪≫ b) ≪≫ c ≪≫ d) ≪≫ e ≪≫ f := by
  simp only [Iso.trans_assoc]

theorem pullbackCongr_app_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) :
    ((Scheme.Modules.pullbackCongr h).app M).symm =
      (Scheme.Modules.pullbackCongr h.symm).app M := by
  cases h
  rfl

variable {S : Scheme.{u}} {H A : Over S} (i : H ⟶ A)
  (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)

theorem swap_square : (β_ H H).hom ≫ (i ⊗ₘ i) = (i ⊗ₘ i) ≫ (β_ A A).hom :=
  (BraidedCategory.braiding_naturality i i).symm

/-- Restrict the original symmetry to the actual full subgroup product. -/
def symmetry :
    (Scheme.Modules.pullback (β_ H H).hom.left).obj (IntersectionFrames.intersectionLine i i Q).sheaf ≅
      (IntersectionFrames.intersectionLine i i Q).sheaf :=
  Line.Fibers.fiberPullbackIso Q (β_ H H).hom (i ⊗ₘ i) ((i ⊗ₘ i) ≫ (β_ A A).hom) (swap_square i) ≪≫
    Line.SymmetryFibers.atPoint Q (β_ A A).hom σ (i ⊗ₘ i)

/-- The existing second kernel frame is exactly the first frame transported through the original symmetry. -/
theorem secondFrame_eq :
    Symmetric.KernelTrivialization.secondFrame i Q s σ =
      GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) Q s (β_ A H).hom
        ((𝟙 A ⊗ₘ i) ≫ (β_ A A).hom) (Symmetric.KernelTrivialization.exchange_square i).symm ≪≫
      Line.SymmetryFibers.atPoint Q (β_ A A).hom σ (𝟙 A ⊗ₘ i) := by
  have hc : ((Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (Symmetric.KernelTrivialization.exchange_square i))).app Q.sheaf).symm =
      (Scheme.Modules.pullbackCongr
        (congrArg Over.Hom.left (Symmetric.KernelTrivialization.exchange_square i).symm)).app Q.sheaf :=
    pullbackCongr_app_symm
      (congrArg Over.Hom.left (Symmetric.KernelTrivialization.exchange_square i)) Q.sheaf
  have hp := reverse_path
    ((Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).mapIso σ)
    ((Scheme.Modules.pullbackComp (𝟙 A ⊗ₘ i).left (β_ A A).hom.left).app Q.sheaf)
    ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (Symmetric.KernelTrivialization.exchange_square i))).app Q.sheaf)
    ((Scheme.Modules.pullbackComp (β_ A H).hom.left (i ⊗ₘ 𝟙 A).left).app Q.sheaf)
    ((Scheme.Modules.pullback (β_ A H).hom.left).mapIso s)
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (β_ A H).hom.left)
  apply hp.trans
  rw [Line.SymmetryFibers.atPoint_eq, GlobalPullbackFrame.atPoint,
    GlobalPullbackFrame.comparison_eq]
  dsimp only [Line.Fibers.fiber]
  simp only [FrameRatioPullback.pullFrame, NatIso.trans_app]
  rw [hc]
  exact regroup_path
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (β_ A H).hom.left).symm
    ((Scheme.Modules.pullback (β_ A H).hom.left).mapIso s)
    ((Scheme.Modules.pullbackComp (β_ A H).hom.left (i ⊗ₘ 𝟙 A).left).app Q.sheaf)
    ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (Symmetric.KernelTrivialization.exchange_square i).symm)).app Q.sheaf)
    ((Scheme.Modules.pullbackComp (𝟙 A ⊗ₘ i).left (β_ A A).hom.left).app Q.sheaf).symm
    ((Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).mapIso σ)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionSymmetry
