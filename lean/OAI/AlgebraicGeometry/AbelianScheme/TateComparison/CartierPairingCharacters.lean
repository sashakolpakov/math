import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierEvaluationRefinement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.WeilPairing

/-! # Cartier Pairing Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierPairingCharacters

noncomputable section

/-! The inverse Cartier characters defining the native Weil pairing
descend to precisely their original dual-torsion points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.WeilPairing.Construction

universe u

theorem groupIso_inverse_point_composite {S : Scheme.{u}} {G H : Grp (Over S)}
    (e : G ≅ H) {T X : Over S} (y : T ⟶ H.X) (p : G.X ⟶ X) (r : H.X ⟶ X)
    (hp : e.hom.hom.hom ≫ r = p) : (y ≫ e.inv.hom.hom) ≫ p = y ≫ r := by
  have hi : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) e.inv_hom_id
  rw [← hp, Category.assoc, ← Category.assoc e.inv.hom.hom, hi, Category.id_comp]

theorem torsionGroup_eqToIso_inclusion {S : Scheme.{u}} (X : Over S)
    (g₁ g₂ : GrpObj X) (c₁ : letI := g₁; IsCommMonObj X)
    (c₂ : letI := g₂; IsCommMonObj X) (hg : g₁ = g₂) (n : ℕ) :
    (eqToIso (IsogenyQuotient.CharacterTorsionComparison.Construction.torsionGroup_eq_of_group_eq X g₁ g₂ c₁ c₂ hg n)).hom.hom.hom ≫
      @TorsionQuotient.SubgroupFunctor.torsionι S X g₂ n = @TorsionQuotient.SubgroupFunctor.torsionι S X g₁ n := by
  cases hg
  exact Category.id_comp _

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s)))

private instance multiplication_isMonHom : IsMonHom ((𝟙 A) ^ n) :=
  Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom (𝟙 A) n

def multiplicationPicardMap :
    (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).dual.X ⟶ D.abelian := by
  let hc := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  letI : IsFinite ((𝟙 A) ^ n).left := hc.1
  letI : Flat ((𝟙 A) ^ n).left := hc.2.1
  letI : Surjective ((𝟙 A) ^ n).left := hc.2.2.1
  letI : LocallyOfFinitePresentation ((𝟙 A) ^ n).left := hc.2.2.2
  exact CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn)

omit [IsAlgClosed k] [Flat ell.left] [Surjective ell.left] in
theorem multiplicationCartierMap_inclusion :
    (IsogenyQuotient.Canonical.CartierMap.Construction.canonicalMultiplicationCartierMap A D ell n hn).hom.hom ≫
      @TorsionQuotient.SubgroupFunctor.torsionι (Spec (.of k)) D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) n =
        multiplicationPicardMap A D ell n hn := by
  obtain ⟨hf, hflat, hs, hfp⟩ := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  dsimp only [IsogenyQuotient.Canonical.CartierMap.Construction.canonicalMultiplicationCartierMap, CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup,
    multiplicationPicardMap, Grp.homMk, Grp.homMk', CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion]
  exact @TorsionQuotient.SubgroupFunctor.torsionLift_ι (Spec (.of k)) D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D)
    (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).dual.X n _ _

theorem geometricCartierIso_hom :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricMultiplicationCartierIso A D ell n hn hdegree).hom.hom.hom =
      (IsogenyQuotient.Canonical.CartierMap.Construction.canonicalMultiplicationCartierMap A D ell n hn).hom.hom ≫
        (eqToIso (IsogenyQuotient.CharacterTorsionComparison.Construction.torsionGroup_eq_of_group_eq D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
          (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) D.commutative (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) n)).hom.hom.hom := rfl

theorem geometricCartierIso_inclusion :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricMultiplicationCartierIso A D ell n hn hdegree).hom.hom.hom ≫
      TorsionQuotient.SubgroupFunctor.torsionι D.abelian n = multiplicationPicardMap A D ell n hn := by
  let f := (IsogenyQuotient.Canonical.CartierMap.Construction.canonicalMultiplicationCartierMap A D ell n hn).hom.hom
  let j := (eqToIso (IsogenyQuotient.CharacterTorsionComparison.Construction.torsionGroup_eq_of_group_eq D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) D.commutative (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) n)).hom.hom.hom
  have hi := torsionGroup_eqToIso_inclusion D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) D.commutative (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) n
  exact (congrArg (fun z => z ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n)
    (geometricCartierIso_hom A D ell n hn hdegree)).trans
    ((Category.assoc f j (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n)).trans
      ((congrArg (fun z => f ≫ z) hi).trans (multiplicationCartierMap_inclusion A D ell n hn)))

def nativeWeilCharacterPoint (T : Over (Spec (.of k))) (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) :
    T ⟶ (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).dual.X :=
  y ≫ (IsogenyQuotient.CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).inv.hom.hom ≫
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricMultiplicationCartierIso A D ell n hn hdegree).inv.hom.hom

theorem nativeWeilCharacterPoint_picard (T : Over (Spec (.of k)))
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) :
    nativeWeilCharacterPoint A D ell n hn hdegree T y ≫
      multiplicationPicardMap A D ell n hn =
        y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n := by
  let j : IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n :=
    (IsogenyQuotient.CharacterTorsionComparison.Construction.equalizerTorsionKernelGroupIso (Grp.mk D.abelian) n).inv.hom.hom
  let i := IsogenyQuotient.Geometric.WeilPairing.Construction.geometricMultiplicationCartierIso A D ell n hn hdegree
  have h := groupIso_inverse_point_composite i (y ≫ j) (multiplicationPicardMap A D ell n hn)
    (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n) (geometricCartierIso_inclusion A D ell n hn hdegree)
  have hstart : nativeWeilCharacterPoint A D ell n hn hdegree T y = (y ≫ j) ≫ i.inv.hom.hom :=
    (Category.assoc y j i.inv.hom.hom).symm
  exact (congrArg (fun z => z ≫ multiplicationPicardMap A D ell n hn) hstart).trans
    (h.trans ((Category.assoc y j (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n)).trans
      (congrArg (fun f => y ≫ f) (IsogenyQuotient.Intrinsic.TorsionComparison.Construction.torsionEqualizerKernelIso_inv_inclusion D.abelian n))))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierPairingCharacters
