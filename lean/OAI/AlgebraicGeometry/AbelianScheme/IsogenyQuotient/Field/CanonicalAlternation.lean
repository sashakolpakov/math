import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilFrames
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.DiagonalTorsionFrame
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroScalarFrame
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceTorsionCoordinates

/-! # Canonical Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalAlternation.Construction

noncomputable section

/-! The canonical CartierDuality polarization pairing is alternating whenever
the original polarization family has its actual diagonal-normalized
symmetry. The proof retains every scheme-theoretic torsion point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf ≅
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd in
theorem fieldNativePolarizationPairing_alternating_affine {Q : Over (Spec (.of k))} [IsAffine Q.left]
    (x : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  let t := x ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom
  let ht : t ^ n = 1 := PoincareWeilCharacter.Construction.originalPolarization_torsionPoint_pow D pol n x
  let U := SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q))
  let z := SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) (Over.mk (𝟙 Q))
    (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom)
  apply (PoincareWeilFrames.Construction.fieldNativePolarizationPairing_eq_one_iff_frames D pol n hn x x).mpr
  exact (Poincare.ZeroScalarFrame.Construction.poincareParameterOriginScalarFrame_vertical D t n ht U).trans
    (Poincare.DiagonalTorsionFrame.Construction.poincareTorsionScalarFrame_polarized D pol.isogeny.hom σ hd n
      (Poincare.KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U) (Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate n U z)
      (Poincare.KernelOriginCoordinates.Construction.poincareParameterDualCoordinate_pow D t n ht U) (Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate_pow n U z)
      (SliceTorsionCoordinates.Construction.poincareDiagonalParameter_coordinates D pol.isogeny.hom n x)).symm

include hd in
theorem fieldNativePolarizationPairing_alternating_of_symmetry {Q : Over (Spec (.of k))}
    (x : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  have hK := Canonical.RelativePairing.Construction.canonicalNativeTorsion_finiteLocallyFree (PolarizationAdapter.Construction.fieldPolarizationOfHilbertConstruction A D pol) n hn
  have : IsFinite (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).hom := hK.1
  have : IsAffine (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).left :=
    isAffine_of_isAffineHom (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).hom
  have h0 := fieldNativePolarizationPairing_alternating_affine D pol n hn σ hd
    (𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n))
  have h := (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue_natural x
    (𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)) (𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n))
  simpa only [Category.comp_id, h0, MonObj.comp_one] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalAlternation.Construction
