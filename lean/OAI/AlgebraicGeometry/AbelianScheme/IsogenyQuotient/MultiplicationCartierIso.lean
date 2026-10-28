import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardRankIso

/-! # Multiplication Cartier Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationCartierIso

noncomputable section

/-!
The canonical Cartier-to-Picard map for multiplication is an isomorphism
over a geometric field when an actual isogeny to the dual has coprime
degree. The map remains the original character-line construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

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
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
    (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s))) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    IsIso (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)) := by
  have : IsFinite ((𝟙 D.abelian : D.abelian ⟶ D.abelian) ^ n).left :=
    CartierDuality.RelativeTorsion.Construction.RelativeAbelian.finite_positive_dual_power A D n hn
  obtain ⟨hAf, hAflat, hAfp⟩ := CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A) n
  obtain ⟨hDf, hDflat, hDfp⟩ := CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk D.abelian) n
  have : IsIso (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell n) := CartierDuality.RelativeTorsion.Construction.RelativeAbelian.torsionMap_isIso A D ell n hn hdegree
  let s : Spec (.of k) := IsLocalRing.closedPoint k
  have hr : (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom.finrank s = (TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n).hom.finrank s := by
    change (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom.finrank s = _
    have : IsIso (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell n).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell n)))
    rw [← (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell n).w, Scheme.Hom.finrank_comp_left_of_isIso]
  refine CartierPicardRankIso.Construction.cartierToPicardTorsionGroup_isIso_of_rank ((𝟙 A) ^ n) D C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) ?_ s ?_
  · rw [Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D]
    exact ⟨hDf, hDflat⟩
  · rw [Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D]
    exact hr

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationCartierIso
