import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockRetraction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ConjugateProjectors

/-! # Canonical Sheaf Block Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockPoints.Construction

noncomputable section

/-! Exact all-test formulas for the canonical sheaf block inclusion and
projection, including their original integral coefficient projector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n : ℕ) (τ : Gal(E/ℚ))

theorem canonicalBlockSheafInclusion_value (T : Over (Spec (.of k)))
    (z : T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp.X) :
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A ρ n τ).hom.app (.op T) (ULift.up z) =
      Prescription.Construction.originalTorsionSheafPoint A (q ^ n) T
        ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n).app (.op T)
          ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (.op T) z)) := by
  have h := yonedaGrpFullyFaithful.map_preimage
    (X := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp)
    (Y := CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) (q ^ n))
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom ≫
      PELModuli.CMPoints.BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n ≫
        (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A (q ^ n)).inv)
  have hz := ConcreteCategory.congr_hom (NatTrans.congr_app h (.op T)) z
  exact congrArg (fun t => (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) (q ^ n)).hom.hom.app
    (.op T) (ULift.up t)) hz

theorem canonicalBlockSheafProjection_value (T : Over (Spec (.of k)))
    (x : (A.torsionFunctor (q ^ n)).obj (.op T)) :
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A ρ n τ).hom.app (.op T)
        (Prescription.Construction.originalTorsionSheafPoint A (q ^ n) T x) =
      ULift.up ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).inv.app (.op T)
        ((PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A ρ n τ).app (.op T) x)) := by
  let e := ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A (q ^ n)).app (.op T)).groupIsoToMulEquiv
  let z := e.symm x
  let i := CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) (q ^ n)
  have hi := congrArg (fun f => f.hom.app (.op T) (ULift.up z)) i.hom_inv_id
  have hb := yonedaGrpFullyFaithful.map_preimage
    (X := CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) (q ^ n))
    (Y := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp)
    ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A (q ^ n)).hom ≫
      PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A ρ n τ ≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).inv)
  have hz := ConcreteCategory.congr_hom (NatTrans.congr_app hb (.op T)) z
  let b := CanonicalSheafBlockRetraction.Construction.nativeTorsionToCanonicalBlock j iota hsplit A ρ n τ
  have : IsCommMonObj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp.X :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).comm
  exact (congrArg (fun t => (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b).hom.app (.op T) t) hi).trans
    ((congrArg ULift.up hz).trans
      (congrArg (fun t => ULift.up ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).inv.app (.op T)
        ((PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A ρ n τ).app (.op T) t)))
          (e.apply_symm_apply x)))

theorem canonicalBlockSheafProjector_value (T : Over (Spec (.of k)))
    (x : (A.torsionFunctor (q ^ n)).obj (.op T)) :
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A ρ n τ ≫
      CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A ρ n τ).hom.app (.op T)
        (Prescription.Construction.originalTorsionSheafPoint A (q ^ n) T x) =
      Prescription.Construction.originalTorsionSheafPoint A (q ^ n) T
        ((PELModuli.CMPoints.DualityPairing.homOnTorsion A A (ρ.map (j.projector iota hsplit n τ)) (q ^ n)).app (.op T) x) := by
  let y := (PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A ρ n τ).app (.op T) x
  let e := ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).app (.op T)).groupIsoToMulEquiv
  have hi := canonicalBlockSheafInclusion_value j iota hsplit A ρ n τ T (e.symm y)
  have hy := congrArg (fun t => Prescription.Construction.originalTorsionSheafPoint A (q ^ n) T
    ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n).app (.op T) t))
      (e.apply_symm_apply y)
  exact (congrArg
    (fun t => (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A ρ n τ).hom.app (.op T) t)
    (canonicalBlockSheafProjection_value j iota hsplit A ρ n τ T x)).trans (hi.trans hy)

theorem canonicalBlockSheafProjector_eq :
    CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A ρ n τ ≫
      CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A ρ n τ =
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
          (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.scheme (ρ.map (j.projector iota hsplit n τ)))) (q ^ n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := (Prescription.Construction.originalTorsionSheafPoint_bijective A (q ^ n) T.unop).surjective x
  exact (canonicalBlockSheafProjector_value j iota hsplit A ρ n τ T.unop x).trans
    (PrescriptionActions.Construction.originalTorsionSheafPoint_endomorphism A (q ^ n) (ρ.map (j.projector iota hsplit n τ)) T.unop x).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockPoints.Construction
