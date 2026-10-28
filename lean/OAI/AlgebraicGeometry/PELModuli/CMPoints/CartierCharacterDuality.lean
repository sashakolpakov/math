import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityCanonicalPairing
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CharacterIsoNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints

/-! # Cartier Character Duality -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierCharacterDuality

noncomputable section

section

/-! The native torsion sheaf comparisons commute with the actual
endomorphisms and with restriction of Cartier characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (f : A.scheme ⟶ A.scheme) [IsMonHom f] (n : ℕ)

def torsionPointGroupMap : CartierDualityTorsionComparison.torsionPointGroups A n ⟶ CartierDualityTorsionComparison.torsionPointGroups A n where
  app T := CommGrpCat.ofHom ((DualityPairing.homOnTorsion A A f n).app T).hom
  naturality := by
    intro T U u
    apply CommGrpCat.hom_ext
    exact congrArg GrpCat.Hom.hom ((DualityPairing.homOnTorsion A A f n).naturality u)

theorem nativeTorsionCommPointsIso_natural :
    (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (CartierDualityTorsionIsogeny.nativeAbelianGroupMap A A f) n)).hom ≫
        (Functor.isoWhiskerRight (CartierDualityTorsionComparison.nativeTorsionCommPointsIso A n)
          CommGrpCat.uliftFunctor.{1, 0}).hom =
      (Functor.isoWhiskerRight (CartierDualityTorsionComparison.nativeTorsionCommPointsIso A n)
          CommGrpCat.uliftFunctor.{1, 0}).hom ≫
        Functor.whiskerRight (torsionPointGroupMap A f n) CommGrpCat.uliftFunctor.{1, 0} := by
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  apply ULift.ext
  exact congrArg (fun h => h.app T x) (CartierDualityTorsionIsogeny.nativeTorsionPointsIso_natural A A f n)

theorem torsionSheafPointIso_natural :
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDualityTorsionIsogeny.nativeAbelianGroupMap A A f)) n).hom ≫
        (CartierDualityTorsionComparison.torsionSheafPointIso A n).hom =
      (CartierDualityTorsionComparison.torsionSheafPointIso A n).hom ≫
        Functor.whiskerRight (torsionPointGroupMap A f n) CommGrpCat.uliftFunctor.{1, 0} := by
  have h := AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_inverse (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) n) _ _
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_natural (CartierDualityTorsionIsogeny.nativeAbelianGroupMap A A f) n)
  exact AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_comp _ _ _ _ _
    (congrArg (fun t => t.hom) h) (nativeTorsionCommPointsIso_natural A f n)

theorem torsionCartierPointIso_natural :
    ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDualityTorsionIsogeny.nativeAbelianGroupMap A A f)) n).op).hom ≫
        (CartierDualityTorsionComparison.torsionCartierPointIso A n).hom =
      (CartierDualityTorsionComparison.torsionCartierPointIso A n).hom ≫
        AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction (DualityPairing.homOnTorsion A A f n)
          (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) := by
  have h := congrArg (fun t => Functor.whiskerRight t (forget₂ CommGrpCat GrpCat))
    (torsionSheafPointIso_natural A f n)
  simp only [Functor.whiskerRight_comp] at h
  exact AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_comp _ _ _ _ _
    (CharacterIsoNaturality.characterGroupCongr_natural
      (Functor.isoWhiskerRight (CartierDualityTorsionComparison.torsionSheafPointIso A n) (forget₂ CommGrpCat GrpCat))
      (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj _ _ h)
    (AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_inverse
      (AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.CommutativeSheaves.uliftInternalHomIso (A.torsionFunctor n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))) _ _
      (CharacterIsoNaturality.uliftInternalHomIso_natural (A.torsionFunctor n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) (DualityPairing.homOnTorsion A A f n)))

end

section

/-! Transport of a proved native character square through the actual
torsion and character comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
  (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem torsionCharacter_adjoint_transport (n : ℕ)
    (e : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk P.abelian.scheme)) n) ≅
      AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk P.dual.abelian.scheme)) n)
    (f : P.abelian.scheme ⟶ P.abelian.scheme) [IsMonHom f]
    (d : P.dual.abelian.scheme ⟶ P.dual.abelian.scheme) [IsMonHom d]
    (he : AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
        (CartierDualityTorsionIsogeny.nativeAbelianGroupMap P.dual.abelian P.dual.abelian d)) n ≫ e.inv =
      e.inv ≫ (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor _).map
        (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
          (CartierDualityTorsionIsogeny.nativeAbelianGroupMap P.abelian P.abelian f)) n).op) :
    let eG := (CartierDualityTorsionComparison.torsionSheafPointIso P.dual.abelian n).symm ≪≫
      (sheafToPresheaf _ CommGrpCat.{1}).mapIso e.symm ≪≫ CartierDualityTorsionComparison.torsionCartierPointIso P.abelian n
    Functor.whiskerRight (DualityPairing.homOnTorsion P.dual.abelian P.dual.abelian d n)
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫
        (CartierDualityCanonicalPairing.torsionCharacterIsoOfGroupIso P n eG).hom =
      (CartierDualityCanonicalPairing.torsionCharacterIsoOfGroupIso P n eG).hom ≫
        DualityPairing.restrictCharacters (DualityPairing.homOnTorsion P.abelian P.abelian f n) := by
  let eG := (CartierDualityTorsionComparison.torsionSheafPointIso P.dual.abelian n).symm ≪≫
    (sheafToPresheaf _ CommGrpCat.{1}).mapIso e.symm ≪≫ CartierDualityTorsionComparison.torsionCartierPointIso P.abelian n
  have h : Functor.whiskerRight (torsionPointGroupMap P.dual.abelian d n)
        CommGrpCat.uliftFunctor.{1, 0} ≫ eG.hom =
      eG.hom ≫ AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.restriction (DualityPairing.homOnTorsion P.abelian P.abelian f n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints _ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver _)) :=
    AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_comp _ _ _ _ _
      (AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_inverse (CartierDualityTorsionComparison.torsionSheafPointIso P.dual.abelian n) _ _
        (torsionSheafPointIso_natural P.dual.abelian d n))
      (AbelianScheme.FrobeniusKernel.Intertwining.Construction.intertwining_comp _ _ _ _ _ (congrArg (fun t => t.hom) he)
        (torsionCartierPointIso_natural P.abelian f n))
  exact congrArg (fun t => Functor.whiskerRight t (forget CommGrpCat)) h

end

/-! The Poincare adjoint acts on the actual CartierDuality Cartier characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

def NativeTorsionCartierAdjointData (n : ℕ) (G : GrpObj P.dual.abelian.scheme)
    (hcomm : @IsCommMonObj _ _ _ _ P.dual.abelian.scheme G.toMonObj) :=
  letI := G
  letI := hcomm
  { e : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk P.abelian.scheme)) n) ≅
        AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk P.dual.abelian.scheme)) n //
    ∀ (f : P.abelian.scheme ⟶ P.abelian.scheme) (hf : IsMonHom f)
      (d : P.dual.abelian.scheme ⟶ P.dual.abelian.scheme) (hd : IsMonHom d),
      letI := hf
      letI := hd
      DualityPairing.PoincareAdjoint P f d →
        AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
          (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup P.dual.abelian.scheme d)) n ≫ e.inv =
          e.inv ≫ (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor _).map
            (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
              (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup P.abelian.scheme f)) n).op }

def NativeTorsionCartierAdjointData.congr (n : ℕ)
    (G H : GrpObj P.dual.abelian.scheme)
    (hG : @IsCommMonObj _ _ _ _ P.dual.abelian.scheme G.toMonObj)
    (hH : @IsCommMonObj _ _ _ _ P.dual.abelian.scheme H.toMonObj)
    (h : G = H) (data : NativeTorsionCartierAdjointData P n G hG) :
    NativeTorsionCartierAdjointData P n H hH := by
  cases h
  exact data

def geometricNativeTorsionCartierAdjointData (n : ℕ) (hn : 0 < n) :
    NativeTorsionCartierAdjointData P n P.dual.abelian.group P.dual.abelian.commutative := by
  let D := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual
  have hD : D.withPicardGroup = D := CartierDualityCanonicalPairing.geometricDualData_withPicardGroup P
  have : IsMonHom (show P.abelian.scheme ⟶ D.abelian from P.polarization.isogeny.hom) :=
    P.polarization.isogeny.preservesGroup
  have : IsFinite (show P.abelian.scheme ⟶ D.abelian from P.polarization.isogeny.hom).left :=
    P.polarization.isogeny.finite
  have hc := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover P.abelian.scheme D
    P.polarization.isogeny.hom n hn
  let ell : P.abelian.scheme ⟶ D.withPicardGroup.abelian := P.polarization.isogeny.hom
  have : IsMonHom ell := by
    dsimp only [ell]
    change @IsMonHom _ _ _ P.abelian.scheme P.dual.abelian.scheme _
      (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D).toMonObj P.polarization.isogeny.hom
    rw [Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D]
    exact P.polarization.isogeny.preservesGroup
  have : IsFinite ell.left := P.polarization.isogeny.finite
  have : Flat ell.left := P.polarization.isogeny.flat
  have : Surjective ell.left := P.polarization.isogeny.surjective
  have : IsFinite ((𝟙 P.abelian.scheme : P.abelian.scheme ⟶ P.abelian.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 P.abelian.scheme : P.abelian.scheme ⟶ P.abelian.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 P.abelian.scheme : P.abelian.scheme ⟶ P.abelian.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation
      ((𝟙 P.abelian.scheme : P.abelian.scheme ⟶ P.abelian.scheme) ^ n).left := hc.2.2.2
  let K := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 P.abelian.scheme) ^ n))
  have hK := AbelianScheme.CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk P.abelian.scheme) n
  have : IsCommMonObj K.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative
    ((𝟙 P.abelian.scheme) ^ n)
  have : IsFinite K.X.hom := hK.1
  have : Flat K.X.hom := hK.2.1
  have : LocallyOfFinitePresentation K.X.hom := hK.2.2
  have data : NativeTorsionCartierAdjointData P n (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D)
      (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) := by
    refine ⟨AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso P.abelian.scheme D ell n hn
      (CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation _ K), ?_⟩
    intro f hf d hd hadj
    let := hf
    let := hd
    have hmap : AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup P.abelian.scheme f D.withPicardGroup =
        @AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup _ P.dual.abelian.scheme (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) d hd := by
      apply Grp.hom_ext
      exact (AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints.Construction.sourceNativeDualMap_eq P f).trans
        (AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.l45PoincareAdjoint_eq_dualMap P f d hadj).symm
    have hx := AbelianScheme.FrobeniusKernel.IntrinsicWeilAdjoints.Construction.nativeWeilCharacter_endomorphism P.abelian.scheme D ell n hn
      (CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation _ K) f
    rw [hmap] at hx
    exact hx
  exact NativeTorsionCartierAdjointData.congr P n (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D)
    P.dual.abelian.group (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) P.dual.abelian.commutative
    (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) data

def poincareTorsionCharacterGroupIso (n : ℕ) (hn : 0 < n) :
    CartierDualityTorsionComparison.torsionPointGroups P.dual.abelian n ⋙ CommGrpCat.uliftFunctor.{1, 0} ≅
      AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (P.abelian.torsionFunctor n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints _ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver _)) :=
  (CartierDualityTorsionComparison.torsionSheafPointIso P.dual.abelian n).symm ≪≫
    (sheafToPresheaf _ CommGrpCat.{1}).mapIso
      (geometricNativeTorsionCartierAdjointData P n hn).val.symm ≪≫
        CartierDualityTorsionComparison.torsionCartierPointIso P.abelian n

def poincareTorsionCharacterIso (n : ℕ) (hn : 0 < n) : DualityPairing.TorsionCharacterIso P n :=
  CartierDualityCanonicalPairing.torsionCharacterIsoOfGroupIso P n (poincareTorsionCharacterGroupIso P n hn)

theorem poincareTorsionCharacter_additive (n : ℕ) (hn : 0 < n) :
    DualityPairing.TorsionCharacterAdditive P n (poincareTorsionCharacterIso P n hn) :=
  CartierDualityCanonicalPairing.torsionCharacterIsoOfGroupIso_additive P n (poincareTorsionCharacterGroupIso P n hn)

theorem poincareTorsionCharacter_adjoint (n : ℕ) (hn : 0 < n) :
    DualityPairing.TorsionCharacterAdjoint P n (poincareTorsionCharacterIso P n hn) := by
  intro f hf d hd hadj
  let := hf
  let := hd
  exact torsionCharacter_adjoint_transport P n
    (geometricNativeTorsionCartierAdjointData P n hn).val f d
    ((geometricNativeTorsionCartierAdjointData P n hn).property f hf d hd hadj)

theorem poincareTorsionCharacter_perfect (n : ℕ) (hn : 0 < n)
    (hgood : n.Coprime (∏ i, δ i)) :
    IsIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P n)
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ (poincareTorsionCharacterIso P n hn).hom) :=
  CartierDualityCanonicalPairing.torsionCharacter_ambient_isIso P n hn hgood (poincareTorsionCharacterIso P n hn)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierCharacterDuality
