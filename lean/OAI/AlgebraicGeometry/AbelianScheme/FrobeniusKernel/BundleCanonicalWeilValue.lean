import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PoincareBundleTorsionPoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockOrthogonality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilData

/-! # Bundle Canonical Weil Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleCanonicalWeilValue

noncomputable section

/-! PoincareBundle's standard Weil value and the independent canonical FrobeniusKernel
pairing have the same all-test orthogonality condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) (hn : 0 < n) (T : Over (Spec (.of k)))
  (x y : (A.abelian.torsionFunctor n).obj (.op T))

theorem e45CanonicalWeilValue_original :
    (Picard.PoincareBundle.Canonical.WeilData.value A.dual A.polarization.isogeny n hn
      (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x) (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T y)).down =
        DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn T y x := by
  have hg := Picard.PoincareBundle.Reference.Torsion.cover A.dual A.polarization.isogeny n hn
  have : IsFinite ((𝟙 A.abelian.scheme) ^ n).left := hg.1
  have : Flat ((𝟙 A.abelian.scheme) ^ n).left := hg.2.1
  have : Surjective ((𝟙 A.abelian.scheme) ^ n).left := hg.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.abelian.scheme) ^ n).left := hg.2.2.2.1
  have : IsAffine (Picard.PoincareBundle.Kernel.Scheme.kernelObject ((𝟙 A.abelian.scheme) ^ n)).left := hg.2.2.2.2
  have : IsFinite ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left :=
    inferInstanceAs (IsFinite ((𝟙 A.abelian.scheme) ^ n).left)
  have : Flat ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left :=
    inferInstanceAs (Flat ((𝟙 A.abelian.scheme) ^ n).left)
  have : Surjective ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left :=
    inferInstanceAs (Surjective ((𝟙 A.abelian.scheme) ^ n).left)
  have : LocallyOfFinitePresentation ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left :=
    inferInstanceAs (LocallyOfFinitePresentation ((𝟙 A.abelian.scheme) ^ n).left)
  let D := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual
  let φ : A.abelian.scheme ⟶ D.withPicardGroup.abelian := A.polarization.isogeny.hom
  have : IsMonHom φ := (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).preservesGroup
  have : IsFinite φ.left := A.polarization.isogeny.finite
  have : Flat φ.left := A.polarization.isogeny.flat
  have : Surjective φ.left := A.polarization.isogeny.surjective
  let C := Picard.PoincareBundle.Canonical.WeilData.representative A.dual A.polarization.isogeny n hn
  have hC : C = DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n := rfl
  have hx := PoincareBundleTorsionPoint.Construction.originalPointToFieldNative_dualTorsion A n T x φ
    (Picard.PoincareBundle.WeilCanonicalTorsionPairing.dual_torsion A.abelian D φ n)
  have hy := PoincareBundleTorsionPoint.Construction.originalPointToFieldNative_equalizer A n T y
  have hv : (Picard.PoincareBundle.Canonical.WeilData.value A.dual A.polarization.isogeny n hn
        (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x) (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T y)).down =
      IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.abelian.scheme D φ n hn C T
        (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y)
        (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap φ n) :=
    congrArg₂ (IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.abelian.scheme D φ n hn C T) hy hx
  exact hv.trans ((congrArg (fun C' => IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.abelian.scheme D φ n hn C' T
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y)
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap φ n)) hC).trans
      (DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue_native A n hn T y x).symm)

theorem e45CanonicalWeilValue_eq_one_iff :
    Picard.PoincareBundle.Canonical.WeilData.value A.dual A.polarization.isogeny n hn
      (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x) (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T y) = 1 ↔
        Prescription.Construction.canonicalTorsionOrthogonal A n hn T x y := by
  have hv := e45CanonicalWeilValue_original A n hn T x y
  constructor
  · intro h
    have hyx := (DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A n hn T y x).mpr
      (hv.symm.trans (congrArg ULift.down h))
    exact CanonicalBlockOrthogonality.Construction.canonicalTorsionOrthogonal_symm A n hn T y x hyx
  · intro h
    have hyx := CanonicalBlockOrthogonality.Construction.canonicalTorsionOrthogonal_symm A n hn T x y h
    exact ULift.ext _ _ (hv.trans ((DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A n hn T y x).mp hyx))

theorem e45CanonicalWeilValue_eq_one_iff_native
    (a b : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) :
    Picard.PoincareBundle.Canonical.WeilData.value A.dual A.polarization.isogeny n hn a b = 1 ↔
      Prescription.Construction.canonicalTorsionOrthogonal A n hn T
        (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal A n T a) (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal A n T b) := by
  have hv := congrArg₂ (fun a' b' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n =>
    Picard.PoincareBundle.Canonical.WeilData.value A.dual A.polarization.isogeny n hn a' b' = 1)
    (PoincareBundleTorsionPoint.Construction.originalPointToFieldNative_toOriginal A n T a) (PoincareBundleTorsionPoint.Construction.originalPointToFieldNative_toOriginal A n T b)
  exact (iff_of_eq hv).symm.trans (e45CanonicalWeilValue_eq_one_iff A n hn T
    (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal A n T a) (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal A n T b))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleCanonicalWeilValue
