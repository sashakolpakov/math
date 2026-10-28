import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacters

/-! # Frobenius Characters -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusCharacters

noncomputable section

/-! Specialize the actual Picard-kernel character embedding to relative
Frobenius, with its canonical group structures and geometric hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
variable (A : Over (Spec (.of k))) [GrpObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

def frobeniusPicardKernelCharacterEmbedding
    (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (op R)).X ≅ Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p Fact.out
      (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A)) [IsMonHom i.hom] :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Frobenius.Construction.frobeniusTwist p Fact.out
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A).left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Frobenius.Construction.relativeFrobenius p Fact.out
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A).left q =
          AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} ↪ GroupLike k R := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Frobenius.Construction.relativeFrobenius p Fact.out hS A
  have hf := Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p Fact.out hS A
  have : IsFinite F.left := hf.1.1
  have : Flat F.left := hf.1.2.1
  have : Surjective F.left := hf.2.1
  have hK := Kernel.Construction.kernelScheme_finiteLocallyFree F hf.1
  have : IsFinite (Kernel.Construction.kernelScheme F).hom := hK.1
  have : IsAffine (Kernel.Construction.kernelScheme F).left := isAffine_of_isAffineHom (Kernel.Construction.kernelScheme F).hom
  have : IsProper (Frobenius.Construction.frobeniusTwist p Fact.out hS A).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd A.hom
      (Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (.of k)) hS)))
  have : IsLocallyNoetherian (Frobenius.Construction.frobeniusTwist p Fact.out hS A).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Frobenius.Construction.frobeniusTwist p Fact.out hS A).hom
  exact KernelCharacters.Construction.picardKernelCharacterEmbedding F R i

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusCharacters
