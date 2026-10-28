import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.SecondDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

/-! # Kernel Trivialization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelTrivialization

noncomputable section

/-!
# The second normalized kernel frame obtained from symmetry of the actual line bundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {H A : Over S} (i : H ⟶ A)
  (L : Line.Bundles.LineBundle (A ⊗ A).left)
  (frame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj L.sheaf)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)

/-- Exchange of factors identifies the two actual subgroup-restriction squares. -/
theorem exchange_square : (𝟙 A ⊗ₘ i) ≫ (β_ A A).hom = (β_ A H).hom ≫ (i ⊗ₘ 𝟙 A) :=
  BraidedCategory.braiding_naturality (𝟙 A) i

/-- Symmetry and the first normalized frame canonically trivialize the second subgroup restriction. -/
def secondRestrictionIso :
    (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ H).left :=
  (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).mapIso symmetry.symm ≪≫
    (Scheme.Modules.pullbackComp (𝟙 A ⊗ₘ i).left (β_ A A).hom.left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (exchange_square i))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp (β_ A H).hom.left (i ⊗ₘ 𝟙 A).left).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback (β_ A H).hom.left).mapIso frame.symm ≪≫
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (β_ A H).hom.left

/-- The second actual kernel frame is constructed by the symmetry of the original line. -/
def secondFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ H).left ≅
    (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).obj L.sheaf :=
  (secondRestrictionIso i L frame symmetry).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelTrivialization
