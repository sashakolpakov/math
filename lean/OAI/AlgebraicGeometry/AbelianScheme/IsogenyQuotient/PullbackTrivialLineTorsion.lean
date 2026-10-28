import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLinePowers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLineRecovery

/-! # Pullback Trivial Line Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackTrivialLineTorsion.Construction

noncomputable section

/-! A framed pullback-trivial line has torsion bounded by the actual
kernel of the cover, using effective character descent on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) A).left.appTop]

theorem pullbackTrivialLine_class_torsion (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (s : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (n : ℕ) (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) ^ n = 1 := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f
      (Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s))
      (Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s))) :=
    Quotient.sound (Kernel.CharacterLineRecovery.Construction.kernelCharacterLineRecovery f L s)
  rw [he]
  exact Kernel.CharacterLinePowers.Construction.kernelCharacterLine_class_torsion f
    (Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s))
    (Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s)) n hn

theorem pullbackTrivialClass_torsion (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left c = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)
    (n : ℕ) (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) : c ^ n = 1 := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep c
  obtain ⟨s⟩ := Quotient.exact hc
  exact pullbackTrivialLine_class_torsion f L s n hn

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackTrivialLineTorsion.Construction
