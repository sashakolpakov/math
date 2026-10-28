import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupRankIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism

/-! # Cartier Picard Rank Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardRankIso.Construction

noncomputable section

/-!
The actual character-line morphism is an isomorphism onto dual torsion
when the kernel and that torsion have equal finite-flat rank. Perfection
of a pairing is not a premise of this criterion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

universe u

theorem cartierToPicardTorsionGroup_isIso_of_rank
    {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (f : A ⟶ B) [IsMonHom f]
    [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    (n : ℕ) (hn : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (hD : letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
      IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n).hom ∧ Flat (TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n).hom)
    (s : Spec (.of k))
    (hr : letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
      (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom.finrank s = (TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n).hom.finrank s) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    IsIso (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : IsCommMonObj C.dual.X := C.commutative
  have : IsFinite C.dual.X.hom := C.finite
  have : Flat C.dual.X.hom := C.flat
  let H := CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk D.abelian) n
  have : IsFinite H.X.hom := hD.1
  have : Flat H.X.hom := hD.2
  have : Mono (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn).hom.hom :=
    CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicardTorsion_mono f D C n hn
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.2.1
  apply Finite.GroupRankIso.Construction.finiteGroup_mono_isIso_of_finrank_eq C.dual H (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn) s
  exact (CartierRank.Construction.cartierGroupRepresentation_finrank (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) C s).trans hr

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardRankIso.Construction
