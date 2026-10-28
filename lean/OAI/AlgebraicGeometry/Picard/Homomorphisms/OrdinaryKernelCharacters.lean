import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusCharacters
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelTransport
import OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDualCount
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCoordinateRank
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterTorsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ElementaryCharacters

/-! # Ordinary Kernel Characters -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryKernelCharacters

noncomputable section

/-! The ordinary p-rank supplies a full basis of characters of the
scheme-theoretic Frobenius kernel. Both bounds use actual geometric
objects: Picard descent for the lower bound and linear independence in
the finite Hopf coordinate algebra for the upper bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem coordinateCharacters_card_le_finrank
    (k R : Type u) [Field k] [CommRing R] [HopfAlgebra k R] [Module.Finite k R] :
    Nat.card (GroupLike k R) ≤ Module.finrank k R := by
  have : Finite (GroupLike k R) := CharacterSpan.Construction.finite_coordinateCharacters k R
  let := Fintype.ofFinite (GroupLike k R)
  simpa only [Nat.card_eq_fintype_card] using
    (linearIndep_groupLikeVal (R := k) (A := R)).fintype_card_le_finrank

variable (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)

include D ell in
theorem ordinary_frobeniusKernel_character_count
    (hordinary : Nat.card (A.torsionPoints p (Over.mk (𝟙 (Spec (.of k))))) = p ^ g)
    (R : CommHopfAlgCat k) [Module.Finite k R]
    (i : ((hopfSpec (.of k)).obj (op R)).X ≅
      Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p Fact.out
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A.scheme)) [IsMonHom i.hom] :
    Nat.card (GroupLike k R) = p ^ g := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let B := A.pullback (Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (.of k)) hS)
  let F : A.scheme ⟶ B.scheme := Frobenius.Construction.relativeFrobenius p Fact.out hS A.scheme
  have : IsMonHom F := Group.Construction.relativeFrobenius_isMonHom p Fact.out hS A.scheme
  have : Finite (GroupLike k R) := CharacterSpan.Construction.finite_coordinateCharacters k R
  let j := (KernelTransport.Construction.geometricDualKernelNativeLineEmbedding D
    (D.pullback (Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (.of k)) hS)) F).trans
      (FrobeniusCharacters.Construction.frobeniusPicardKernelCharacterEmbedding p k A.scheme R i)
  have hj := Nat.card_le_card_of_injective j j.injective
  have hc := OrdinaryDualCount.Construction.ordinary_dualFrobenius_kernelPointCount p A D ell hordinary
  have hr := KernelCoordinateRank.Construction.frobeniusKernel_coordinate_finrank p Fact.out k hS A.scheme g R i
  apply Nat.le_antisymm
  · exact (coordinateCharacters_card_le_finrank k R).trans_eq hr
  · exact hc.symm.trans_le hj

include D ell in
theorem ordinary_frobeniusKernel_multiplicative
    (hordinary : Nat.card (A.torsionPoints p (Over.mk (𝟙 (Spec (.of k))))) = p ^ g) :
    Nonempty (Grp.mk (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p Fact.out
      (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A.scheme)) ≅
        Grp.mk (Diagonalizable.Construction.splitMultiplicativePTorsion p k g)) := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Frobenius.Construction.relativeFrobenius p Fact.out hS A.scheme
  have hK := Kernel.Construction.kernelScheme_finiteLocallyFree F
    (Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p Fact.out hS A.scheme).1
  have : IsFinite (Kernel.Construction.kernelScheme F).hom := hK.1
  obtain ⟨R, hf, hc, ⟨e⟩⟩ := FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k (Grp.mk (Kernel.Construction.kernelScheme F))
  have : Module.Finite k R := hf
  have : Coalgebra.IsCocomm k R := hc
  let i : ((hopfSpec (.of k)).obj (op R)).X ≅ Kernel.Construction.kernelScheme F :=
    (Grp.forget (Over (Spec (.of k)))).mapIso e
  have : IsMonHom i.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have hcard := ordinary_frobeniusKernel_character_count p A D ell hordinary R i
  have hrank := KernelCoordinateRank.Construction.frobeniusKernel_coordinate_finrank p Fact.out k hS A.scheme g R i
  exact ⟨e.symm ≪≫ ElementaryCharacters.Construction.multiplicativeGroupIsoOfCharacterCard k R p g
    (KernelCharacterTorsion.Construction.frobeniusKernel_coordinate_character_pow p k A.scheme R e) hcard hrank⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryKernelCharacters
