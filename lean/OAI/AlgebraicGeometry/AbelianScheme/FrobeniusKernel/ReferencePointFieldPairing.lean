import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointBicharacter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionActions
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter

/-! # Reference Point Field Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointFieldPairing.Construction

noncomputable section

/-! The original torsion-point values equal the canonical field pairing
on the corresponding native torsion scheme, with the inclusion retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) (hn : 0 < n) (T : Over (Spec (.of k)))

def originalPointToFieldNative (x : (A.abelian.torsionFunctor n).obj (.op T)) :
    T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n :=
  IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme n x.val x.property

omit [IsAlgClosed k] in
theorem originalPointToFieldNative_sheaf (x : (A.abelian.torsionFunctor n).obj (.op T)) :
    (IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.abelian.scheme) n).hom.hom.app (.op T)
      (ULift.up (originalPointToFieldNative A n T x)) = Prescription.Construction.originalTorsionSheafPoint A.abelian n T x := by
  apply PrescriptionActions.Construction.originalTorsionSheafInclusion_injective A.abelian n T
  have h := congrArg (fun f => f.hom.app (.op T) (ULift.up (originalPointToFieldNative A n T x)))
    (IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso_inclusion (Grp.mk A.abelian.scheme) n)
  exact h.trans ((congrArg ULift.up
    (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme n x.val x.property)).trans
      (PrescriptionActions.Construction.originalTorsionSheafPoint_inclusion A.abelian n T x).symm)

theorem originalPointPairing_field (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A.abelian A.dual A.polarization n hn).pairValue
      (originalPointToFieldNative A n T x) (originalPointToFieldNative A n T y) =
        DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn T x y := by
  have h := IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue
    (Grp.mk A.abelian.scheme) (Grp.mk A.abelian.scheme) n
    (CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn) T (originalPointToFieldNative A n T x) (originalPointToFieldNative A n T y)
  have hxy := congrArg₂ (fun a b =>
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) T
      ((CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn).rightAdjoint.hom.app (.op T) b) a)
    (originalPointToFieldNative_sheaf A n T x) (originalPointToFieldNative_sheaf A n T y)
  exact congrArg ULift.down (h.trans hxy)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointFieldPairing.Construction
