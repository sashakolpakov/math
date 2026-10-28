import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricCharacterMonomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsionRank
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteGroupRankIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricIsomorphisms
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData

/-! # Relative Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeIso

noncomputable section

/-! Perfection of the actual character-line morphism over an arbitrary base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

universe u

namespace Construction.KernelCharacters

/-- The canonical character-line map identifies Cartier dual torsion with the actual Picard-dual
 torsion over any base and for every positive n. No invertibility or coprimality is required. -/
theorem relativeMultiplicationCartierToPicardTorsionGroup_isIso
    {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))) :
    IsIso (PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D.withPicardGroup C n (CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)) := by
  let E := D.withPicardGroup
  have : IsFinite ((𝟙 E.abelian : E.abelian ⟶ E.abelian) ^ n).left :=
    RelativeTorsion.Construction.RelativeAbelian.finite_positive_dual_power A E n hn
  have hA := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A) n
  have hB := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk E.abelian) n
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hA.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hA.2.1
  have : IsCommMonObj C.dual.X := C.commutative
  have : IsFinite C.dual.X.hom := C.finite
  have : Flat C.dual.X.hom := C.flat
  have : LocallyOfFinitePresentation C.dual.X.hom := C.finitelyPresented
  let H := TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk E.abelian) n
  have : IsCommMonObj H.X := TorsionSheaves.Construction.Schemes.nativeTorsionGroup_commutative (Grp.mk E.abelian) n
  have : IsFinite H.X.hom := hB.1
  have : Flat H.X.hom := hB.2.1
  have : LocallyOfFinitePresentation H.X.hom := hB.2.2
  let g : C.dual ⟶ H := PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) E C n (CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
  have hg : IsIso g.hom.hom.left := by
    apply GeometricIsomorphisms.Construction.Schemes.isIso_of_algClosed_baseChanges g.hom.hom
    intro k _ _ s
    let F := Over.pullback s
    let G' := F.mapGrp.obj C.dual
    let H' := F.mapGrp.obj H
    let g' : G' ⟶ H' := F.mapGrp.map g
    have : IsCommMonObj G'.X := Functor.isCommMonObj_obj (F := F) (M := C.dual.X)
    have : IsCommMonObj H'.X := Functor.isCommMonObj_obj (F := F) (M := H.X)
    have : IsFinite G'.X.hom := inferInstanceAs (IsFinite (pullback.snd C.dual.X.hom s))
    have : Flat G'.X.hom := inferInstanceAs (Flat (pullback.snd C.dual.X.hom s))
    have : IsFinite H'.X.hom := inferInstanceAs (IsFinite (pullback.snd H.X.hom s))
    have : Flat H'.X.hom := inferInstanceAs (Flat (pullback.snd H.X.hom s))
    have : Mono g'.hom.hom :=
      GeometricCharacterMonomorphism.Construction.KernelCharacters.cartierToPicardTorsion_geometric_mono s ((𝟙 A) ^ n) E C n (CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
    let K := F.mapGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))
    have : IsCommMonObj K.X := Functor.isCommMonObj_obj (F := F) (M := Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))
    have : IsFinite K.X.hom := inferInstanceAs
      (IsFinite (pullback.snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom s))
    have : Flat K.X.hom := inferInstanceAs
      (Flat (pullback.snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom s))
    let t : Spec (.of k) := IsLocalRing.closedPoint k
    have hr : G'.X.hom.finrank t = H'.X.hom.finrank t :=
      (Rank.Construction.Schemes.characterRepresentative_finrank k K (C.baseChange s) t).trans
        (RelativeTorsionRank.Construction.Schemes.geometric_torsion_finrank_eq_of_isogeny A E.abelian ell n s t)
    have : IsIso g' := FiniteGroupRankIso.Construction.Schemes.finiteGroup_mono_isIso_of_finrank_eq G' H' g' t hr
    exact inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).map g'))
  have : IsIso ((Over.forget S).map g.hom.hom) := hg
  have : IsIso g.hom.hom := isIso_of_reflects_iso g.hom.hom (Over.forget S)
  exact (Grp.mkIso' (asIso g.hom.hom)).isIso_hom

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeIso
