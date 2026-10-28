import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.CartierMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierIsoPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharacterTorsionComparison

/-! # Weil Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.WeilPairing

noncomputable section

/-!
Construct the native Weil pairing on geometric fibers from the inverse
of actual character-line descent. Both the Cartier representative and
its isomorphism with dual torsion are constructed from the original
isogeny to the Picard dual and its coprime degree.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s)))

def geometricMultiplicationCartierIso :
    (Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).dual ≅
      CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk D.abelian) n := by
  let i : letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
      letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
      (Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).dual ≅
        CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk D.abelian) n := by
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    have : IsIso (Canonical.CartierMap.Construction.canonicalMultiplicationCartierMap A D ell n hn) :=
      Canonical.CartierMap.Construction.canonicalMultiplicationCartierMap_isIso_geometric A D ell n hn hdegree
    exact asIso (Canonical.CartierMap.Construction.canonicalMultiplicationCartierMap A D ell n hn)
  exact i ≪≫ eqToIso (CharacterTorsionComparison.Construction.torsionGroup_eq_of_group_eq D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) D.commutative (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) n)

set_option backward.isDefEq.respectTransparency false in
def geometricNativeWeilPairing :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme D.abelian n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) := by
  let i : Torsion.Groups.Construction.nativeTorsionScheme A n ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n) :=
    (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n).inv.hom.hom
  let j : Torsion.Groups.Construction.nativeTorsionScheme D.abelian n ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n :=
    (CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).inv.hom.hom
  have : IsMonHom i := inferInstanceAs (IsMonHom (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n).inv.hom.hom)
  have : IsMonHom j := inferInstanceAs (IsMonHom (CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).inv.hom.hom)
  exact (CartierIsoPairing.Construction.cartierIsoSchemePairing (Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn)
    (geometricMultiplicationCartierIso A D ell n hn hdegree)).restrict i j

theorem geometricNativeWeilPairing_isPerfect :
    (geometricNativeWeilPairing A D ell n hn hdegree).toSheafPairing.IsPerfect := by
  have hcover := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree ((𝟙 A) ^ n) ⟨hcover.1, hcover.2.1, hcover.2.2.2⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hK.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hK.2.2
  exact Annihilator.Construction.SchemeBicharacter.restrict_isPerfect_of_iso _
    (CartierIsoPairing.Construction.cartierIsoSchemePairing_isPerfect (Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn)
      (geometricMultiplicationCartierIso A D ell n hn hdegree))
    (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n).symm
    (CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).symm

set_option backward.isDefEq.respectTransparency false in
theorem geometricNativeWeilPairing_value (T : Over (Spec (.of k)))
    (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A n) (y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) :
    (geometricNativeWeilPairing A D ell n hn hdegree).pairValue x y =
      (Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).evaluationValue T
        (y ≫ (CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).inv.hom.hom ≫
          (geometricMultiplicationCartierIso A D ell n hn hdegree).inv.hom.hom)
        (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n).inv.hom.hom) := by
  let i : Torsion.Groups.Construction.nativeTorsionScheme A n ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n) :=
    (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n).inv.hom.hom
  let j : Torsion.Groups.Construction.nativeTorsionScheme D.abelian n ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n :=
    (CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).inv.hom.hom
  have : IsMonHom i := inferInstanceAs (IsMonHom (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n).inv.hom.hom)
  have : IsMonHom j := inferInstanceAs (IsMonHom (CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).inv.hom.hom)
  let C := Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn
  let e := geometricMultiplicationCartierIso A D ell n hn hdegree
  exact ((CartierIsoPairing.Construction.cartierIsoSchemePairing C e).restrict_pairValue i j x y).trans
    ((CartierIsoPairing.Construction.cartierIsoSchemePairing_value C e T (x ≫ i) (y ≫ j)).trans
      (congrArg (fun z => C.evaluationValue T z (x ≫ i)) (Category.assoc y j e.inv.hom.hom)))

def geometricIsogenyTorsionPairing :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme A n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  (geometricNativeWeilPairing A D ell n hn hdegree).restrict (𝟙 _) (Torsion.Groups.Construction.nativeTorsionMap n ell)

set_option backward.isDefEq.respectTransparency false in
theorem geometricIsogenyTorsionPairing_isPerfect :
    (geometricIsogenyTorsionPairing A D ell n hn hdegree).toSheafPairing.IsPerfect := by
  have : IsIso (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell n) := CartierDuality.RelativeTorsion.Construction.RelativeAbelian.torsionMap_isIso A D ell n hn hdegree
  have : IsIso (Torsion.Groups.Construction.nativeTorsionMap n ell) := Intrinsic.TorsionComparison.Construction.nativeTorsionMap_isIso_of_equalizer n ell
  let j : Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A) n ≅ Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk D.abelian) n :=
    Grp.mkIso' (asIso (Torsion.Groups.Construction.nativeTorsionMap n ell))
  exact Annihilator.Construction.SchemeBicharacter.restrict_isPerfect_of_iso
    (G := Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A) n) (H := Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk D.abelian) n)
    (geometricNativeWeilPairing A D ell n hn hdegree)
    (geometricNativeWeilPairing_isPerfect A D ell n hn hdegree) (Iso.refl _) j

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.WeilPairing
