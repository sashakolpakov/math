import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter

/-! # Pairing Values -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues

noncomputable section

/-! Compare the canonical CartierDuality pairing in the original FrobeniusKernel torsion
functor with its native IsogenyQuotient scheme presentation, retaining every test
scheme and the literal source polarization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {g : ℕ}

theorem originalTorsionSheafPoint_inclusion (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (m : ℕ) (T : Over (Spec (.of k))) (x : (A.torsionFunctor m).obj (.op T)) :
    (kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A.scheme)) m)).hom.app (.op T)
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint A m T x) = ULift.up x.val := by
  have hi := congrArg (fun f => f.hom.app (.op T)
    (ULift.up ((AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A m).inv.app (.op T) x)))
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_inclusion (Grp.mk A.scheme) m)
  change (kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A.scheme)) m)).hom.app (.op T)
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint A m T x) =
    ULift.up (((AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A m).inv.app (.op T) x) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A.scheme m) at hi
  refine hi.trans (congrArg ULift.up ?_)
  exact congrArg Subtype.val (((AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A m).app (.op T)).inv_hom_id_apply x)

theorem originalTorsionSheafPoint_native (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (m : ℕ) (T : Over (Spec (.of k))) (x : (A.torsionFunctor m).obj (.op T)) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint A m T x =
      (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.scheme) m).hom.hom.app (.op T)
        (ULift.up (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.scheme m x.val x.property)) := by
  let inc := kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A.scheme)) m)
  have : Mono inc := inferInstanceAs (Mono (kernel.ι _))
  have hm : Mono (inc.hom.app (.op T)) := inferInstance
  apply (CommGrpCat.mono_iff_injective (inc.hom.app (.op T))).mp hm
  rw [originalTorsionSheafPoint_inclusion]
  have hi := congrArg (fun f => f.hom.app (.op T)
    (ULift.up (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.scheme m x.val x.property)))
    (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso_inclusion (Grp.mk A.scheme) m)
  change inc.hom.app (.op T)
      ((AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.scheme) m).hom.hom.app (.op T)
        (ULift.up (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.scheme m x.val x.property))) =
    ULift.up (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.scheme m x.val x.property ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.scheme m) at hi
  exact (hi.trans (congrArg ULift.up (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.scheme m x.val x.property))).symm

variable [IsAlgClosed k] {N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

def prescribedNativePairing (m : ℕ) (hm : 0 < m) :
    AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme m)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme m)
      (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative (Grp.mk A.abelian.scheme) (Grp.mk A.abelian.scheme) m
    (AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing A m hm)

theorem prescribedNativePairing_eq_reducedBase (m : ℕ) (hm : 0 < m) :
    prescribedNativePairing A m hm = AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing
      A.abelian A.dual A.polarization m hm := rfl

theorem prescribedNativePairing_isPerfect (m : ℕ) (hm : 0 < m)
    (hdegree : m.Coprime (∏ i, δ i)) :
    (prescribedNativePairing A m hm).toSheafPairing.IsPerfect :=
  AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_isPerfect (Grp.mk A.abelian.scheme) (Grp.mk A.abelian.scheme)
    m (AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing A m hm) (AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing_isPerfect A m hm hdegree)

theorem canonicalTorsionOrthogonal_native (m : ℕ) (hm : 0 < m)
    (T : Over (Spec (.of k))) (x y : (A.abelian.torsionFunctor m).obj (.op T)) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A m hm T x y ↔
      (prescribedNativePairing A m hm).pairValue
        (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme m x.val x.property)
        (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme m y.val y.property) = 1 := by
  have hv := AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue (Grp.mk A.abelian.scheme)
    (Grp.mk A.abelian.scheme) m (AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing A m hm) T
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme m x.val x.property)
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme m y.val y.property)
  unfold AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal
  rw [originalTorsionSheafPoint_native, originalTorsionSheafPoint_native]
  constructor
  · intro h
    exact ULift.up_injective (hv.trans h)
  · intro h
    exact hv.symm.trans (congrArg ULift.up h)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues
