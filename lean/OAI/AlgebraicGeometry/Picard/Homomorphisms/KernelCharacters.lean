import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineMorphismDescent

/-! # Kernel Characters -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacters

noncomputable section

/-! Actual pullback-trivialized line-bundle classes inject into characters
of the native scheme-theoretic kernel. Equality of characters descends
the isomorphism between their trivializations on the cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem pullbackTrivialClass_representative {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X}) :
    ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = q.val ∧
      Nonempty ((Scheme.Modules.pullback f).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep q.val
  refine ⟨L, hL, ?_⟩
  exact Quotient.exact ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f) hL).trans q.property)

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable [IsAffine (Kernel.Construction.kernelScheme f).left]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
variable [IsLocallyNoetherian B.left]
variable (R : CommHopfAlgCat k)
variable (i : ((hopfSpec (.of k)).obj (op R)).X ≅ Kernel.Construction.kernelScheme f) [IsMonHom i.hom]

theorem lineKernelCoordinateCharacter_eq_implies_iso
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (d : (Scheme.Modules.pullback f.left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (h : LineKernelCharacters.Construction.lineKernelCoordinateCharacter L e R i.hom =
      LineKernelCharacters.Construction.lineKernelCoordinateCharacter M d R i.hom) : Nonempty (L.sheaf ≅ M.sheaf) := by
  have hs := LineKernelCharacters.Construction.kernelCocycleCoordinateCharacter_eq_implies_scalar_eq
    (LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e) (LineKernelCocycle.Construction.pullbackLineKernelCocycle f M d) R i h
  obtain ⟨a, _⟩ := LineMorphismDescent.Construction.exists_lineIso_of_compatible_pullbackIso f.left L M (e ≪≫ d.symm)
    (fun q x y hx hy => KernelCharacterDetection.Construction.kernelScalar_eq_implies_native_compatible
      (LineKernelCocycle.Construction.pullbackLineNativeDatum f L) (LineKernelCocycle.Construction.pullbackLineNativeDatum f M) e d hs q x y hx hy)
  exact ⟨a⟩

def picardKernelCharacterEmbedding :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} ↪ GroupLike k R := by
  classical
  choose L hL e using pullbackTrivialClass_representative f.left
  refine ⟨fun q => LineKernelCharacters.Construction.lineKernelCoordinateCharacter (L q) (e q).some R i.hom, ?_⟩
  intro q r h
  apply Subtype.ext
  exact (hL q).symm.trans ((Quotient.sound
    (lineKernelCoordinateCharacter_eq_implies_iso f R i (L q) (L r)
      (e q).some (e r).some h)).trans (hL r))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacters
