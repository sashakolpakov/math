import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilFrames
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionValueComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroScalarFrame
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceIdentityUnits

/-! # Canonical Poincare Bundle Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPoincareBundleValue.Construction

noncomputable section

/-! The actual canonical CartierDuality polarization pairing and the canonical
PoincareBundle Poincare kernel value agree on every affine test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf ≅
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf)
  (σn : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n)).sheaf ≅
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n)).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hdn : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σn =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n)) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n))
      (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)) σn =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))

include hd hdn in
theorem fieldCanonicalPairing_e45_value_affine {Q : Over (Spec (.of k))} [IsAffine Q.left]
    (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q ((PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y) =
    Picard.PoincareBundle.Canonical.KernelPairing.value (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
      ((𝟙 A.scheme) ^ n) (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation pol.isogeny.hom n) σn hv x y := by
  let U := SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q))
  let i := (SliceKernelPoints.Construction.parameterSliceTestIso Q (Over.mk (𝟙 Q))).hom
  let t := y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom
  let ht : t ^ n = 1 := PoincareWeilCharacter.Construction.originalPolarization_torsionPoint_pow D pol n y
  let zx := SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) (Over.mk (𝟙 Q))
    (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom)
  let zy := SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) (Over.mk (𝟙 Q))
    (y ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom)
  let a := Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate n U zx
  let b := Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate n U zy
  have ha : (i ≫ x) ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = a :=
    (Category.assoc i x (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n)).trans
      (SliceTorsionCoordinates.Construction.parameterSliceTorsionCoordinate_original A n Q (Over.mk (𝟙 Q)) x).symm
  have hb : (i ≫ y) ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = b :=
    (Category.assoc i y (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n)).trans
      (SliceTorsionCoordinates.Construction.parameterSliceTorsionCoordinate_original A n Q (Over.mk (𝟙 Q)) y).symm
  have hF := congrArg (fun v => Picard.PoincareBundle.Line.FrameUnits.frameRatio v (Poincare.KernelScalarRatio.Construction.poincareParameterTorsionScalarFrame D t n ht U zx))
    (Poincare.ZeroScalarFrame.Construction.poincareParameterOriginScalarFrame_vertical D t n ht U)
  have hV := Poincare.TorsionValueComparison.Construction.poincareTorsionScalarFrame_e45Value_of_coordinate D pol.isogeny.hom n σ σn hd hdn hv
    (i ≫ x) (i ≫ y) (Poincare.KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U) a b ha hb
    (Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate_pow n U zx) (Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate_pow n U zy)
    (Poincare.KernelOriginCoordinates.Construction.poincareParameterDualCoordinate_pow D t n ht U) (SliceTorsionCoordinates.Construction.poincareDiagonalParameter_coordinates D pol.isogeny.hom n y)
  have hN := Picard.PoincareBundle.Canonical.KernelPairing.value_naturality (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
    ((𝟙 A.scheme) ^ n) (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation pol.isogeny.hom n) σn hv i x y
  have hI := SliceIdentityUnits.Construction.parameterSliceTestIso_units Q (Over.mk (𝟙 Q))
    (Picard.PoincareBundle.Canonical.KernelPairing.value (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
      ((𝟙 A.scheme) ^ n) (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation pol.isogeny.hom n) σn hv x y)
  apply Units.ext
  exact (PoincareWeilFrames.Construction.fieldNativePolarizationPairing_poincare_frames D pol n hn x y).trans
    (congrArg Units.val (hF.trans (hV.trans (hN.trans hI))))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPoincareBundleValue.Construction
