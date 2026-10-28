import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData

/-! # Cartier Sheaf Point -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierSheafPoint

noncomputable section

/-! The actual Cartier-Picard sheaf map preserves the native dual torsion point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f)))
  (n : ℕ) (hn : ∀ (T : Over S) (x : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

/-- Under the canonical representations, the actual sheaf point is the native Cartier torsion image. -/
theorem value (T : Over S) (d : T ⟶ C.dual.X) :
    (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D.withPicardGroup C n hn).hom.app (.op T)
      (C.representedCartierDualIso.hom.hom.app (.op T) (ULift.up d)) =
    (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T)
      (ULift.up (d ≫ AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f D.withPicardGroup n hn C)) := by
  have : IsCommMonObj C.dual.X := C.commutative
  have h := AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf_representation f D.withPicardGroup C n hn
  exact congrArg (fun m => m.hom.app (.op T) (ULift.up d)) h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierSheafPoint
