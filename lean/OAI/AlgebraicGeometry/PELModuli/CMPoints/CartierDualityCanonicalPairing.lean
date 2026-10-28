import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionIsogeny
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

/-! # Cartier Duality Canonical Pairing -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityCanonicalPairing

noncomputable section

/-! The canonical CartierDuality Weil characters on the specified geometric dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem geometricDualData_withPicardGroup :
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).withPicardGroup = Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual := by
  unfold Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.withPicardGroup
  congr 1
  exact Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual)

def geometricNativeTorsionCartierIso (n : ℕ) (hn : 0 < n) :
    AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk P.abelian.scheme)) n) ≅
      AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk P.dual.abelian.scheme)) n := by
  let D := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual
  have hD : D.withPicardGroup = D := geometricDualData_withPicardGroup P
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
  have e := AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso P.abelian.scheme D ell n hn
    (CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation _ K)
  rw [hD] at e
  exact e

def geometricTorsionCharacterGroupIso (n : ℕ) (hn : 0 < n) :
    CartierDualityTorsionComparison.torsionPointGroups P.dual.abelian n ⋙ CommGrpCat.uliftFunctor.{1, 0} ≅
      AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (P.abelian.torsionFunctor n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints _ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver _)) :=
  (CartierDualityTorsionComparison.torsionSheafPointIso P.dual.abelian n).symm ≪≫
    (sheafToPresheaf _ CommGrpCat.{1}).mapIso (geometricNativeTorsionCartierIso P n hn).symm ≪≫
      CartierDualityTorsionComparison.torsionCartierPointIso P.abelian n

def torsionCharacterIsoOfGroupIso (n : ℕ)
    (e : CartierDualityTorsionComparison.torsionPointGroups P.dual.abelian n ⋙ CommGrpCat.uliftFunctor.{1, 0} ≅
      AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (P.abelian.torsionFunctor n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints _ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver _))) : DualityPairing.TorsionCharacterIso P n :=
  Functor.isoWhiskerRight e (forget CommGrpCat)

omit [IsAlgClosed k] in
theorem torsionCharacterIsoOfGroupIso_additive (n : ℕ)
    (e : CartierDualityTorsionComparison.torsionPointGroups P.dual.abelian n ⋙ CommGrpCat.uliftFunctor.{1, 0} ≅
      AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (P.abelian.torsionFunctor n)
        (AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints _ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver _))) :
    DualityPairing.TorsionCharacterAdditive P n (torsionCharacterIsoOfGroupIso P n e) := by
  intro T y z U x
  have h := (e.hom.app (.op T)).hom.map_mul (ULift.up y) (ULift.up z)
  exact congrArg (fun χ => (χ.app (.op U)) x) h

def geometricTorsionCharacterIso (n : ℕ) (hn : 0 < n) : DualityPairing.TorsionCharacterIso P n :=
  torsionCharacterIsoOfGroupIso P n (geometricTorsionCharacterGroupIso P n hn)

theorem geometricTorsionCharacter_additive (n : ℕ) (hn : 0 < n) :
    DualityPairing.TorsionCharacterAdditive P n (geometricTorsionCharacterIso P n hn) :=
  torsionCharacterIsoOfGroupIso_additive P n (geometricTorsionCharacterGroupIso P n hn)

omit [IsAlgClosed k] in
theorem torsionCharacter_ambient_isIso (n : ℕ) (hn : 0 < n)
    (hgood : n.Coprime (∏ i, δ i)) (e : DualityPairing.TorsionCharacterIso P n) :
    IsIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P n)
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom) := by
  have : IsIso (DualityPairing.polarizationOnTorsion P n) := CartierDualityTorsionIsogeny.polarizationOnTorsion_isIso P n hn hgood
  infer_instance

theorem geometricTorsionCharacter_perfect (n : ℕ) (hn : 0 < n)
    (hgood : n.Coprime (∏ i, δ i)) :
    IsIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P n)
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ (geometricTorsionCharacterIso P n hn).hom) :=
  torsionCharacter_ambient_isIso P n hn hgood (geometricTorsionCharacterIso P n hn)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityCanonicalPairing
