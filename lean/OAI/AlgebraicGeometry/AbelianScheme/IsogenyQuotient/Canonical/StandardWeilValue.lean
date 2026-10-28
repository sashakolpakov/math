import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafSectionComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilData

/-! # Standard Weil Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilValue.Construction

noncomputable section

/-! The two canonical Weil APIs evaluate the same character of the
actual torsion sheaf, with their displayed variable order made explicit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalStandardWeilValue_eq (T : Over (Spec (.of k)))
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    Picard.PoincareBundle.Canonical.WeilData.value D pol.isogeny n hn x y =
      ULift.up ((IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue y x) := by
  let p := IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldPolarizationOfHilbertConstruction A D pol
  have : IsMonHom (show A.scheme ⟶ p.dual.abelian from p.map) := p.preservesGroup
  have : IsFinite (show A.scheme ⟶ p.dual.abelian from p.map).left := p.finite
  have : Flat (show A.scheme ⟶ p.dual.abelian from p.map).left := p.flat
  have : Surjective (show A.scheme ⟶ p.dual.abelian from p.map).left := p.surjective
  have hcover := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.scheme p.dual p.map n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hcover.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hcover.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hcover.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hcover.2.2.2
  let K := Picard.PoincareBundle.Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)
  have : IsFinite K.hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite ((𝟙 A.scheme) ^ n)
  have : IsAffine K.left := isAffine_of_isAffineHom K.hom
  let t := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A.scheme) ^ n) ≫ p.map
  have ht : t ^ n = 1 := by
    rw [show t = Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ p.map from rfl,
      ← MonObj.pow_comp, Torsion.Groups.Construction.nativeTorsionInclusion_killed, MonObj.one_comp]
  let z := x ≫ Torsion.Groups.Construction.nativeTorsionMap n p.map
  have hz : (x ≫ TorsionQuotient.SubgroupFunctor.torsionLift n t ht) ≫ TorsionQuotient.SubgroupFunctor.torsionι p.dual.abelian n =
      z ≫ Torsion.Groups.Construction.nativeTorsionInclusion p.dual.abelian n := by
    rw [Category.assoc, TorsionQuotient.SubgroupFunctor.torsionLift_ι]
    change x ≫ (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ p.map) =
      (x ≫ Torsion.Groups.Construction.nativeTorsionMap n p.map) ≫ Torsion.Groups.Construction.nativeTorsionInclusion p.dual.abelian n
    rw [Category.assoc, Torsion.Groups.Construction.nativeTorsionMap_inclusion]
  have hzs := Torsion.SheafSectionComparison.Construction.torsionSheafSection_eq_of_inclusion (Grp.mk p.dual.abelian) n T
    (x ≫ TorsionQuotient.SubgroupFunctor.torsionLift n t ht) z hz
  have hys := MultiplicationKernelSheafComparison.Construction.multiplicationKernelSheafIso_native_value (Grp.mk A.scheme) n T y
  change CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A) n) T
    ((p.weilPairing n hn).rightAdjoint.hom.app (.op T)
      ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk p.dual.abelian) n).hom.hom.app (.op T)
        (ULift.up (x ≫ TorsionQuotient.SubgroupFunctor.torsionLift n t ht))))
    ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T)
      (ULift.up (y ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom))) = _
  rw [hzs, hys]
  exact (Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue (Grp.mk A.scheme) (Grp.mk p.dual.abelian)
    n (p.weilPairing n hn) T y z).symm.trans
      (congrArg ULift.up (RelativePairing.Construction.canonicalNativePolarizationPairing_value p n hn T y x).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilValue.Construction
