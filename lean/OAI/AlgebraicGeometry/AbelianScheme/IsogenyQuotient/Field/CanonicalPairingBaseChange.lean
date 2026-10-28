import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.WeilCharacterValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionReferencePoint
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeFlip
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeUnitBaseChange

/-! # Canonical Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPairingBaseChange.Construction

noncomputable section

/-! The actual canonical polarization pairing commutes with every field
extension, as equality of scheme maps and on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

variable {k K : Type} [Field k] [Field K] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  (s : Spec (.of K) ⟶ Spec (.of k))

set_option backward.isDefEq.respectTransparency false in
theorem fieldNativePolarizationPairing_baseChange_value (T : Over (Spec (.of K)))
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).pairValue x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s T
        ((PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue
          (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T x)
          (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y)) := by
  apply CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective T
  rw [FrobeniusKernel.MultiplicativeUnitBaseChange.Construction.multiplicativeGroupUnitHom_baseChange]
  have hv := Picard.PoincareBundle.Field.WeilBaseChange.value D pol.isogeny n hn s T
    (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
    (Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion (A.pullback s).scheme n y)
    (x ≫ Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
    (Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion (A.pullback s).scheme n x)
  have hx := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint_inclusion s (Grp.mk A.scheme) n T x
  have hy := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint_inclusion s (Grp.mk A.scheme) n T y
  have hright := WeilCharacterValue.Construction.fieldNativePolarizationPairing_character_value D pol n hn ((Over.map s).obj T)
    (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y)
    (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T x)
  simp only [hx, hy] at hright
  exact (WeilCharacterValue.Construction.fieldNativePolarizationPairing_character_value (D.pullback s) (pol.pullback s) n hn T y x).trans
    (hv.trans hright.symm)

set_option backward.isDefEq.respectTransparency false in
theorem fieldNativePolarizationPairing_baseChange :
    PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn =
      Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback s (Grp.mk A.scheme) (Grp.mk A.scheme) n
        (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn) := by
  apply Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro T x y
  exact (fieldNativePolarizationPairing_baseChange_value D pol n hn s T x y).trans
    (Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback_value s (Grp.mk A.scheme) (Grp.mk A.scheme) n
      (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn) T x y).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPairingBaseChange.Construction
