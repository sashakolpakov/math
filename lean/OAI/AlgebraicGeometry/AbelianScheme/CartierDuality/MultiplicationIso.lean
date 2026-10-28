import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardRankIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IsogenyTorsionRank

/-! # Multiplication Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationIso

noncomputable section

/-!
The canonical Cartier-to-Picard map for multiplication is an isomorphism
over a geometric field for every positive n when there is an actual
isogeny to the dual. The map remains the original character-line construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction.KernelCharacters

universe u

theorem multiplicationCartierToPicardTorsionGroup_isIso
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    IsIso (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D C n (CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)) := by
  have : IsFinite ((𝟙 D.abelian : D.abelian ⟶ D.abelian) ^ n).left :=
    RelativeTorsion.Construction.RelativeAbelian.finite_positive_dual_power A D n hn
  have hD := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk D.abelian) n
  let s : Spec (.of k) := IsLocalRing.closedPoint k
  have hr : (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom.finrank s = (TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n).hom.finrank s :=
    IsogenyTorsionRank.Construction.Schemes.torsionKernel_finrank_eq_of_isogeny A D.abelian ell n s
  refine PicardRankIso.Construction.KernelCharacters.cartierToPicardTorsionGroup_isIso_of_rank ((𝟙 A) ^ n) D C n (CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) ?_ s ?_
  · rw [Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D]
    exact ⟨hD.1, hD.2.1⟩
  · rw [Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D]
    exact hr

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationIso
