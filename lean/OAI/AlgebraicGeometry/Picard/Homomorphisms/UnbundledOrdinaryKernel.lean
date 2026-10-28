import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroupComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledIsogenyCount
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledKernelTransport
import OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryKernelCharacters

/-! # Unbundled Ordinary Kernel -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledOrdinaryKernel

noncomputable section

/-! Ordinary Frobenius kernels from geometric p-rank, using a dimension
only on the fiber being considered. The dual needs no dimension parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u

variable (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian)
variable [IsMonHom ell] [IsFinite ell.left] [Surjective ell.left]

include ell in
theorem ordinary_dualFrobenius_kernelPointCount (g : ℕ)
    (hordinary : Nat.card (powMonoidHom p :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker = p ^ g) :
    Nat.card {x : Over.mk (𝟙 (Spec (.of k))) ⟶
      (D.pullback (Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (.of k))
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)))).abelian //
      x ≫ UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p Fact.out
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) = 1} = p ^ g := by
  rw [UnbundledDualGroupComparison.Construction.UnbundledPicard.dualRelativeFrobenius_eq_verschiebung D p]
  exact (FrobeniusPoints.Construction.verschiebungKernelPoints_card p k D.abelian).trans
    (UnbundledIsogenyCount.Construction.isogeny_preserves_ordinary_count_unbundled ell p Fact.out g hordinary)

include D ell in
theorem ordinary_frobeniusKernel_character_count (g : ℕ) [SmoothOfRelativeDimension g A.hom]
    (hordinary : Nat.card (powMonoidHom p :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker = p ^ g)
    (R : CommHopfAlgCat k) [Module.Finite k R]
    (i : ((hopfSpec (.of k)).obj (op R)).X ≅
      Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p Fact.out
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A)) [IsMonHom i.hom] :
    Nat.card (GroupLike k R) = p ^ g := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F : A ⟶ UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A (Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (.of k)) hS) :=
    Frobenius.Construction.relativeFrobenius p Fact.out hS A
  have : IsMonHom F := Group.Construction.relativeFrobenius_isMonHom p Fact.out hS A
  have : Finite (GroupLike k R) := CharacterSpan.Construction.finite_coordinateCharacters k R
  let j := (UnbundledKernelTransport.Construction.UnbundledPicard.geometricDualKernelNativeLineEmbedding D
    (D.pullback (Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (.of k)) hS)) F).trans
      (FrobeniusCharacters.Construction.frobeniusPicardKernelCharacterEmbedding p k A R i)
  have hj := Nat.card_le_card_of_injective j j.injective
  have hc := ordinary_dualFrobenius_kernelPointCount p A D ell g hordinary
  have hr := KernelCoordinateRank.Construction.frobeniusKernel_coordinate_finrank p Fact.out k hS A g R i
  exact Nat.le_antisymm ((OrdinaryKernelCharacters.Construction.coordinateCharacters_card_le_finrank k R).trans_eq hr)
    (hc.symm.trans_le hj)

include D ell in
theorem ordinary_frobeniusKernel_multiplicative (g : ℕ) [SmoothOfRelativeDimension g A.hom]
    (hordinary : Nat.card (powMonoidHom p :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker = p ^ g) :
    Nonempty (Grp.mk (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p Fact.out
      (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A)) ≅
        Grp.mk (Diagonalizable.Construction.splitMultiplicativePTorsion p k g)) := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Frobenius.Construction.relativeFrobenius p Fact.out hS A
  have hK := Kernel.Construction.kernelScheme_finiteLocallyFree F
    (Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p Fact.out hS A).1
  have : IsFinite (Kernel.Construction.kernelScheme F).hom := hK.1
  obtain ⟨R, hf, hc, ⟨e⟩⟩ := FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k (Grp.mk (Kernel.Construction.kernelScheme F))
  have : Module.Finite k R := hf
  have : Coalgebra.IsCocomm k R := hc
  let i : ((hopfSpec (.of k)).obj (op R)).X ≅ Kernel.Construction.kernelScheme F :=
    (Grp.forget (Over (Spec (.of k)))).mapIso e
  have : IsMonHom i.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have hcard := ordinary_frobeniusKernel_character_count p A D ell g hordinary R i
  have hrank := KernelCoordinateRank.Construction.frobeniusKernel_coordinate_finrank p Fact.out k hS A g R i
  exact ⟨e.symm ≪≫ ElementaryCharacters.Construction.multiplicativeGroupIsoOfCharacterCard k R p g
    (KernelCharacterTorsion.Construction.frobeniusKernel_coordinate_character_pow p k A R e) hcard hrank⟩

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledOrdinaryKernel
