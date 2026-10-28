import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilScalar
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelScalarRatio

/-! # Poincare Weil Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilFrames.Construction

noncomputable section

/-! The canonical CartierDuality polarization pairing equals the ratio of two
explicit frames from the original Poincare scalar comparison, on every
affine test scheme. Equality of those frames detects its vanishing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ)
  {Q : Over (Spec (.of k))}

def fieldPoincareOriginFrame (y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :=
  Poincare.KernelScalarRatio.Construction.poincareParameterOriginScalarFrame D (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom) n
    (PoincareWeilCharacter.Construction.originalPolarization_torsionPoint_pow D pol n y) (SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q)))

def fieldPoincareTorsionFrame (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :=
  Poincare.KernelScalarRatio.Construction.poincareParameterTorsionScalarFrame D (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom) n
    (PoincareWeilCharacter.Construction.originalPolarization_torsionPoint_pow D pol n y) (SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q)))
    (SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) (Over.mk (𝟙 Q))
      (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom))

variable (hn : 0 < n) [IsAffine Q.left]

theorem fieldNativePolarizationPairing_poincare_frames (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q ((PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y) : Γ(Q.left, ⊤)) =
      (Picard.PoincareBundle.Line.FrameUnits.frameRatio (fieldPoincareOriginFrame D pol n y) (fieldPoincareTorsionFrame D pol n x y)).val :=
  (PoincareWeilScalar.Construction.fieldNativePolarizationPairing_poincare_scalar D pol n hn x y).trans
    (Poincare.KernelScalarRatio.Construction.poincareParameterKernelCocycle_frameRatio D
      (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom) n
      (PoincareWeilCharacter.Construction.originalPolarization_torsionPoint_pow D pol n y) (SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q))) _)

theorem fieldNativePolarizationPairing_eq_one_iff_frames (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y = 1 ↔
      fieldPoincareOriginFrame D pol n y = fieldPoincareTorsionFrame D pol n x y := by
  have h := fieldNativePolarizationPairing_poincare_frames D pol n hn x y
  constructor
  · intro he
    apply (Picard.PoincareBundle.Line.FrameUnits.frameRatio_eq_one_iff _ _).mp
    apply Units.ext
    rw [he, map_one] at h
    exact h.symm
  · intro he
    apply CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective Q
    apply Units.ext
    exact h.trans ((congrArg Units.val ((Picard.PoincareBundle.Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr he)).trans
      (congrArg Units.val (map_one (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q))).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilFrames.Construction
