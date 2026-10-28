import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGeometricKernel

/-! # Family Kernel -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.FamilyKernel.Family

noncomputable section

/-! The actual Poincare universal property detects a represented map's full kernel by triviality of its family line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A T H : Over S} [GrpObj A]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (m : T ⟶ D.abelian) (h : H ⟶ T)
  (R : Line.Bundles.LineBundle (T ⊗ A).left)
  (e : R.sheaf ≅ (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) m).sheaf)

/-- Restriction of the represented family is the actual family of the composed parameter map. -/
def restrictedIso : (Scheme.Modules.pullback (h ⊗ₘ 𝟙 A).left).obj R.sheaf ≅
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (h ≫ m)).sheaf :=
  (Scheme.Modules.pullback (h ⊗ₘ 𝟙 A).left).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (h ⊗ₘ 𝟙 A).left (m ⊗ₘ 𝟙 A).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (by
      rw [tensorHom_comp_tensorHom, Category.id_comp] :
      (h ⊗ₘ 𝟙 A) ≫ (m ⊗ₘ 𝟙 A) = ((h ≫ m) ⊗ₘ 𝟙 A)))).app D.poincare.sheaf

/-- Every subgroup killed by the represented map has an actual trivialization of the restricted family. -/
def kernelFrame (hh : h ≫ m = 1) :
    (Scheme.Modules.pullback (h ⊗ₘ 𝟙 A).left).obj R.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left :=
  (Scheme.Modules.pullback (h ⊗ₘ 𝟙 A).left).mapIso e ≪≫
    KernelTrivialization.restrictionIso h m hh (Line.Comparison.Bundle.fromShared D.poincare)
      (Classical.choice D.normalizedAtDualZero)

include e in
/-- Actual family triviality detects the complete represented kernel, on arbitrary test schemes. -/
theorem kernel_iff_trivial : h ≫ m = 1 ↔
    Nonempty ((Scheme.Modules.pullback (h ⊗ₘ 𝟙 A).left).obj R.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left) := by
  constructor
  · intro hh
    exact ⟨kernelFrame D m h R e hh⟩
  · rintro ⟨d⟩
    apply Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_injective D H
    have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((h ≫ m) ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (H ⊗ A).left :=
      Quotient.sound ⟨(restrictedIso D m h R e).symm ≪≫ d⟩
    exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op H)) he).trans
      (Homomorphisms.UnbundledGeometricKernel.Construction.UnbundledPicard.poincareClass_one D H).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.FamilyKernel.Family
