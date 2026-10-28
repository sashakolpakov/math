import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafSource

/-! # Cartier Torsion Source -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierTorsionSource

noncomputable section

/-! Naturality of character descent for a square of different covers,
with a common literal kernel bound. Both Picard torsion maps are the
actual CartierDuality constructions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafSource.Construction

theorem change_source_square {C : Type*} [Category C] {X X' Y Y' Z W : C}
    (e : X ≅ X') (e' : Y ≅ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    (u : X ⟶ Z) (v : Y ⟶ W) (b : Z ⟶ W)
    (ha : a ≫ e'.hom = e.hom ≫ a') (hs : a ≫ v = u ≫ b) :
    a' ≫ (e'.inv ≫ v) = (e.inv ≫ u) ≫ b := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← ha, Category.assoc, e'.hom_inv_id_assoc,
    ← Category.assoc, e.hom_inv_id_assoc]
  exact hs

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B')

def nativePicardSourceMap :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
    Grp.mk D.abelian ⟶ Grp.mk D'.abelian :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
  @Grp.homMk (Over S) _ _ (Grp.mk D.abelian) (Grp.mk D'.abelian)
    (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D b) (AbelianScheme.FrobeniusKernel.IntrinsicPicardHomomorphism.Construction.IntrinsicPicard.dualPullback_isMonHom b D' D)

variable (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (C' : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))
variable (n : ℕ)
variable (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
variable (hn' : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f'), x ^ n = 1)

theorem cartierTorsionGroup_source :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    letI : IsCommMonObj D'.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D'
    C.dualMap C' (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h) ≫
      AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f' D' C' n hn' =
      AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn ≫ AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativePicardSourceMap b D D') n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : IsCommMonObj D'.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D'
  have : Mono (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι D'.abelian n) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 D'.abelian) ^ n) 1))
  apply Grp.hom_ext
  apply (cancel_mono (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι D'.abelian n)).mp
  let c := AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f D n hn C
  let c' := AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f' D' n hn' C'
  let d := Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D b
  have : IsMonHom d := AbelianScheme.FrobeniusKernel.IntrinsicPicardHomomorphism.Construction.IntrinsicPicard.dualPullback_isMonHom b D' D
  change ((C.dualMap C' (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)).hom.hom ≫ c') ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι D'.abelian n =
    (c ≫ AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap d n) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι D'.abelian n
  rw [Category.assoc, Category.assoc, AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion]
  rw [show c' ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι D'.abelian n = AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C' from
    AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion f' D' n hn' C']
  rw [← Category.assoc c (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι D.abelian n) d]
  rw [show c ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι D.abelian n = AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C from
    AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion f D n hn C]
  exact AbelianScheme.FrobeniusKernel.CharacterDualSource.Construction.canonicalCartierPicardMap_source f f' a b h D D' C C'

variable [IsCommMonObj A] [IsCommMonObj A']

theorem cartierTorsionSheaf_source :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    letI : IsCommMonObj D'.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D'
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
        (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)).op ≫
        AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f' D' C' n hn' =
      AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f D C n hn ≫
        AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativePicardSourceMap b D D')) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D'
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : IsCommMonObj D'.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D'
  have : IsCommMonObj C.dual.X := C.commutative
  have : IsCommMonObj C'.dual.X := C'.commutative
  let r := C.dualMap C' (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)
  let c := AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f D C n hn
  let c' := AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup f' D' C' n hn'
  let t := AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativePicardSourceMap b D D') n
  have hc : AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r ≫ AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c' =
      AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c ≫ AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap t :=
    (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp r c').symm.trans
      ((congrArg (fun w => AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap w)
        (cartierTorsionGroup_source f f' a b h D D' C C' n hn hn')).trans
          (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp c t))
  have hs : AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r ≫
        (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c' ≫ (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D'.abelian) n).hom) =
      (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c ≫ (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.abelian) n).hom) ≫
        AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativePicardSourceMap b D D')) n := by
    rw [← Category.assoc, hc, Category.assoc]
    exact congrArg (fun w => AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c ≫ w)
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_natural (nativePicardSourceMap b D D') n) |>.trans
        (Category.assoc _ _ _).symm
  exact change_source_square C.representedCartierDualIso C'.representedCartierDualIso
    (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r) _ _ _ _
    (AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafSource.Construction.nativeCartierRepresentation_natural C C' (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)) hs

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierTorsionSource
