import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

/-! # Kernel Trivialization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization

noncomputable section

/-!
# Canonical kernel trivialization from actual Poincare normalization and annihilation

If the first-coordinate map kills a subgroup scheme, the family line restricted to that subgroup
is the pullback of the genuine normalized zero fiber. The trivialization is constructed from the
canonical sheaf pullback maps, with no splitting assumption on that subgroup.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {H A Z X : Over S} [GrpObj Z]

/-- The actual zero section in the first coordinate of the Poincare product. -/
def zeroSection : X ⟶ Z ⊗ X := lift (1 : X ⟶ Z) (𝟙 X)

variable (i : H ⟶ A) (φ : A ⟶ Z) (hi : i ≫ φ = 1)

include hi in
/-- A killed subgroup factors the actual family map through the normalized zero section. -/
theorem kernel_zero_factorization :
    (i ⊗ₘ 𝟙 X) ≫ (φ ⊗ₘ 𝟙 X) = snd H X ≫ (zeroSection (Z := Z) (X := X)) := by
  rw [tensorHom_comp_tensorHom, hi, Category.id_comp]
  unfold zeroSection
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst, MonObj.comp_one]
  · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]

variable (P : Line.Bundles.LineBundle (Z ⊗ X).left)
  (normalized : (Scheme.Modules.pullback (zeroSection (Z := Z) (X := X)).left).obj P.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)

/-- The restriction to the actual subgroup product is canonically the structure sheaf. -/
def restrictionIso :
    (Scheme.Modules.pullback (i ⊗ₘ 𝟙 X).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ X).left :=
  (Scheme.Modules.pullbackComp (i ⊗ₘ 𝟙 X).left (φ ⊗ₘ 𝟙 X).left).app P.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (kernel_zero_factorization i φ hi))).app P.sheaf ≪≫
    (Scheme.Modules.pullbackComp (snd H X).left (zeroSection (Z := Z) (X := X)).left).symm.app P.sheaf ≪≫
    (Scheme.Modules.pullback (snd H X).left).mapIso normalized ≪≫
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (snd H X).left

/-- The normalized kernel frame is constructed by actual pullback of the Poincare zero frame. -/
def kernelFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ X).left ≅
    (Scheme.Modules.pullback (i ⊗ₘ 𝟙 X).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf :=
  (restrictionIso i φ hi P normalized).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization
