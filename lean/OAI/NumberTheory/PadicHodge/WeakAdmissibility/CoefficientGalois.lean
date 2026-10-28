import OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField

/-! # Coefficient Galois -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientGalois

noncomputable section

/-! Galois naturality of the constructed finite coefficient fields. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.TiltCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Scalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonGalois
variable (p : ℕ) [Fact p.Prime]

def galoisResidue (σ : PeriodInvariants.PeriodRing.PadicGalois p) : PrimitiveElements.ResidueCp p ≃+* PrimitiveElements.ResidueCp p :=
  IsLocalRing.ResidueField.mapEquiv (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)

theorem galoisResidue_residue (σ : PeriodInvariants.PeriodRing.PadicGalois p) (a : 𝓞_ℂ_[p]) :
    galoisResidue p σ (IsLocalRing.residue 𝓞_ℂ_[p] a) =
      IsLocalRing.residue 𝓞_ℂ_[p] (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ a) :=
  IsLocalRing.ResidueField.map_residue _ a

theorem tiltResidue_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : PreTilt 𝓞_ℂ_[p] p) :
    PrimitiveElements.tiltResidue p (PeriodInvariants.PeriodRing.tiltMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom x) =
      galoisResidue p σ (PrimitiveElements.tiltResidue p x) := by
  rw [PrimitiveElements.tiltResidue_untilt, PeriodInvariants.PeriodRing.untilt_natural, PrimitiveElements.tiltResidue_untilt, galoisResidue_residue]
  rfl

def tiltGaloisAlg (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    PreTilt 𝓞_ℂ_[p] p →ₐ[ZMod p] PreTilt 𝓞_ℂ_[p] p :=
  { PeriodInvariants.PeriodRing.tiltMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom with
    commutes' := fun a => DFunLike.congr_fun
      (Subsingleton.elim
        ((PeriodInvariants.PeriodRing.tiltMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom).comp
          (algebraMap (ZMod p) (PreTilt 𝓞_ℂ_[p] p)))
        (algebraMap (ZMod p) (PreTilt 𝓞_ℂ_[p] p))) a }

variable {k : Type*} [Field k] [Fintype k] [CharP k p] (j : k →+* PrimitiveElements.ResidueCp p)

def conjugateResidue (σ : PeriodInvariants.PeriodRing.PadicGalois p) : k →+* PrimitiveElements.ResidueCp p :=
  (galoisResidue p σ).toRingHom.comp j

theorem coefficientEmbedding_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (a : k) :
    PeriodInvariants.PeriodRing.tiltMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom
      (TiltCoefficients.coefficientEmbedding p j a) = TiltCoefficients.coefficientEmbedding p (conjugateResidue p j σ) a := by
  apply TiltCoefficients.integral_tilt_residue_injective p
    ((TiltCoefficients.coefficientLift_integral p j a).map (tiltGaloisAlg p σ))
    (TiltCoefficients.coefficientLift_integral p (conjugateResidue p j σ) a)
  change PrimitiveElements.tiltResidue p (PeriodInvariants.PeriodRing.tiltMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom
    (TiltCoefficients.coefficientEmbedding p j a)) = PrimitiveElements.tiltResidue p (TiltCoefficients.coefficientEmbedding p (conjugateResidue p j σ) a)
  rw [tiltResidue_galois]
  change galoisResidue p σ (PrimitiveElements.tiltResidue p (TiltCoefficients.coefficientLift p j a)) =
    PrimitiveElements.tiltResidue p (TiltCoefficients.coefficientLift p (conjugateResidue p j σ) a)
  rw [TiltCoefficients.coefficientLift_residue, TiltCoefficients.coefficientLift_residue]
  rfl

theorem coefficientToAInf_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : WittVector p k) :
    PeriodInvariants.PeriodRing.ainfEquiv p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ) (UnramifiedCoefficients.coefficientToAInf p j x) =
      UnramifiedCoefficients.coefficientToAInf p (conjugateResidue p j σ) x := by
  change WittVector.map (PeriodInvariants.PeriodRing.tiltMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom)
    (WittVector.map (TiltCoefficients.coefficientEmbedding p j) x) = WittVector.map (TiltCoefficients.coefficientEmbedding p (conjugateResidue p j σ)) x
  ext n
  simp only [WittVector.map_coeff, coefficientEmbedding_galois]

theorem coefficientToUncompleted_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : WittVector p k) :
    Galois.uncompletedMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ) (UnramifiedCoefficients.coefficientToUncompleted p j x) =
      UnramifiedCoefficients.coefficientToUncompleted p (conjugateResidue p j σ) x :=
  (Galois.PeriodStructure.uncompletedMap_algebraMap p _ (UnramifiedCoefficients.coefficientToAInf p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p)) (coefficientToAInf_galois p j σ x))

theorem coefficientToACris_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : WittVector p k) :
    Galois.completedMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ) (UnramifiedCoefficients.coefficientToACris p j x) =
      UnramifiedCoefficients.coefficientToACris p (conjugateResidue p j σ) x :=
  (Galois.PeriodStructure.completedMap_algebraMap p _ (UnramifiedCoefficients.coefficientToUncompleted p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)) (coefficientToUncompleted_galois p j σ x))

theorem coefficientToPositive_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : WittVector p k) :
    Galois.positiveMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ) (UnramifiedCoefficients.coefficientToPositive p j x) =
      UnramifiedCoefficients.coefficientToPositive p (conjugateResidue p j σ) x :=
  (Galois.positiveMap_algebraMap p _ (UnramifiedCoefficients.coefficientToACris p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p)) (coefficientToACris_galois p j σ x))

theorem coefficientToBCris_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : WittVector p k) :
    Galois.galoisBCrisMap p σ (UnramifiedCoefficients.coefficientToBCris p j x) = UnramifiedCoefficients.coefficientToBCris p (conjugateResidue p j σ) x :=
  (Galois.galoisBCrisMap_algebraMap p σ (UnramifiedCoefficients.coefficientToPositive p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)) (coefficientToPositive_galois p j σ x))

theorem coefficientFieldToBCris_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p)
    (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    Galois.galoisBCrisMap p σ (UnramifiedCoefficients.coefficientFieldToBCris p j x) =
      UnramifiedCoefficients.coefficientFieldToBCris p (conjugateResidue p j σ) x := by
  have he : (Galois.galoisBCrisMap p σ).comp (UnramifiedCoefficients.coefficientFieldToBCris p j) =
      UnramifiedCoefficients.coefficientFieldToBCris p (conjugateResidue p j σ) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k))
    apply RingHom.ext
    intro a
    change Galois.galoisBCrisMap p σ (UnramifiedCoefficients.coefficientFieldToBCris p j
      (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a)) =
        UnramifiedCoefficients.coefficientFieldToBCris p (conjugateResidue p j σ)
          (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a)
    rw [UnramifiedCoefficients.coefficientFieldToBCris_integer, UnramifiedCoefficients.coefficientFieldToBCris_integer, coefficientToBCris_galois]
  exact DFunLike.congr_fun he x

theorem coefficientFieldToCompletion_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p)
    (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    ComparisonGalois.completionGaloisAction p σ (CoefficientComparison.coefficientFieldToCompletion p j x) =
      CoefficientComparison.coefficientFieldToCompletion p (conjugateResidue p j σ) x := by
  apply ComparisonBd.deRham_algebraMap_injective p
  change ComparisonBd.bdRPlusToBdR p (DeRham.galoisBdRPlusAction p σ (CoefficientComparison.coefficientFieldToCompletion p j x)) =
    ComparisonBd.bdRPlusToBdR p (CoefficientComparison.coefficientFieldToCompletion p (conjugateResidue p j σ) x)
  calc
    _ = ComparisonGalois.galoisBdRAction p σ (ComparisonBd.bdRPlusToBdR p (CoefficientComparison.coefficientFieldToCompletion p j x)) :=
      (ComparisonGalois.galoisBdRAction_of p σ _).symm
    _ = ComparisonGalois.galoisBdRAction p σ (ComparisonBd.bCrisToBdR p (UnramifiedCoefficients.coefficientFieldToBCris p j x)) :=
      congrArg (ComparisonGalois.galoisBdRAction p σ) (CoefficientComparison.coefficientFieldToBCris_comparison p j x).symm
    _ = ComparisonBd.bCrisToBdR p (Galois.galoisBCrisMap p σ (UnramifiedCoefficients.coefficientFieldToBCris p j x)) :=
      (ComparisonGalois.bCrisToBdR_galois p σ _).symm
    _ = ComparisonBd.bCrisToBdR p (UnramifiedCoefficients.coefficientFieldToBCris p (conjugateResidue p j σ) x) :=
      congrArg (ComparisonBd.bCrisToBdR p) (coefficientFieldToBCris_galois p j σ x)
    _ = _ := CoefficientComparison.coefficientFieldToBCris_comparison p (conjugateResidue p j σ) x

theorem coefficientFieldToAlgebraic_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p)
    (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    σ (AlgebraicCoefficientFields.coefficientFieldToAlgebraic p j x) =
      AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (conjugateResidue p j σ) x := by
  apply (DeRhamField.Constants.algebraicToBdRPlus p).injective
  change DeRhamField.Constants.algebraicToBdRPlus p (σ (AlgebraicCoefficientFields.coefficientFieldToAlgebraic p j x)) =
    DeRhamField.Constants.algebraicToBdRPlus p (AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (conjugateResidue p j σ) x)
  rw [← DeRhamField.Scalars.algebraicToBdRPlus_galois, AlgebraicCoefficientFields.coefficientFieldToAlgebraic_completion,
    AlgebraicCoefficientFields.coefficientFieldToAlgebraic_completion, coefficientFieldToCompletion_galois]

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientGalois
