import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafSectionComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilCanonicalComparison

/-! # Weil Character Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.WeilCharacterValue.Construction

noncomputable section

/-! Over every field the canonical native polarization pairing evaluates
the actual inverse Cartier character of the original polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)

set_option backward.isDefEq.respectTransparency false in
theorem fieldNativePolarizationPairing_character_value (T : Over (Spec (.of k)))
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T ((PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue y x) =
      Picard.PoincareBundle.Field.WeilPairing.value D pol.isogeny n hn
        (x ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion A.scheme n x)
        (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion A.scheme n y) := by
  let p := PolarizationAdapter.Construction.fieldPolarizationOfHilbertConstruction A D pol
  have : IsMonHom (show A.scheme ⟶ p.dual.abelian from p.map) := p.preservesGroup
  have : IsFinite (show A.scheme ⟶ p.dual.abelian from p.map).left := p.finite
  have : Flat (show A.scheme ⟶ p.dual.abelian from p.map).left := p.flat
  have : Surjective (show A.scheme ⟶ p.dual.abelian from p.map).left := p.surjective
  have hcover := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.scheme p.dual p.map n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hcover.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hcover.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hcover.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hcover.2.2.2
  let C := Picard.PoincareBundle.Canonical.WeilData.representative D pol.isogeny n hn
  let x0 := x ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n
  let y0 := y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n
  have hx0 : x0 ^ n = 1 := Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion A.scheme n x
  have hy0 : y0 ^ n = 1 := Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion A.scheme n y
  have hp : (x0 ≫ p.map) ^ n = 1 := Picard.PoincareBundle.TorsionCharacterNaturality.image_torsion p.map n x0 hx0
  let z := x ≫ Torsion.Groups.Construction.nativeTorsionMap n p.map
  have hz : TorsionQuotient.SubgroupFunctor.torsionLift n (x0 ≫ p.map) hp ≫ TorsionQuotient.SubgroupFunctor.torsionι p.dual.abelian n =
      z ≫ Torsion.Groups.Construction.nativeTorsionInclusion p.dual.abelian n := by
    rw [TorsionQuotient.SubgroupFunctor.torsionLift_ι]
    exact (Category.assoc x (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) p.map).trans
      ((congrArg (fun a => x ≫ a) (Torsion.Groups.Construction.nativeTorsionMap_inclusion n p.map)).symm.trans
        (Category.assoc x (Torsion.Groups.Construction.nativeTorsionMap n p.map) (Torsion.Groups.Construction.nativeTorsionInclusion p.dual.abelian n)).symm)
  have hzs := Torsion.SheafSectionComparison.Construction.torsionSheafSection_eq_of_inclusion (Grp.mk p.dual.abelian) n T
    (TorsionQuotient.SubgroupFunctor.torsionLift n (x0 ≫ p.map) hp) z hz
  have hys := MultiplicationKernelSheafComparison.Construction.multiplicationKernelSheafIso_native_value (Grp.mk A.scheme) n T y
  have hyl := Picard.PoincareBundle.Field.WeilCanonicalComparison.native_lift A.scheme n y
  have hyss : (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T)
      (ULift.up (TorsionQuotient.SubgroupFunctor.torsionLift n y0 hy0)) =
      (Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T) (ULift.up y) := by
    exact (congrArg (fun a : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n) =>
      (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T) (ULift.up a)) hyl).trans hys
  have hv := Picard.PoincareBundle.WeilTorsionCharacter.value A.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) p.map n hn C
    (x0 ≫ p.map) hp (𝟙 T) (TorsionQuotient.SubgroupFunctor.torsionLift n y0 hy0)
  simp only [Category.id_comp] at hv
  change CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A) n) T
    ((p.weilPairing n hn).rightAdjoint.hom.app (.op T)
      ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk p.dual.abelian) n).hom.hom.app (.op T)
        (ULift.up (TorsionQuotient.SubgroupFunctor.torsionLift n (x0 ≫ p.map) hp))))
    ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T)
      (ULift.up (TorsionQuotient.SubgroupFunctor.torsionLift n y0 hy0))) = _ at hv
  rw [hzs, hyss] at hv
  have hnative := (Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue (Grp.mk A.scheme) (Grp.mk p.dual.abelian)
    n (p.weilPairing n hn) T y z).trans hv
  have hchar := congrArg (fun a => CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T a.down) hnative
  exact (congrArg (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T)
    (Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing_value p n hn T y x)).trans hchar

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.WeilCharacterValue.Construction
