import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD

/-! # Dcris Coefficients -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisCoefficients

noncomputable section

/-! Actual coefficient-field scalars and semilinear Frobenius on crystalline invariants. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [Module.Finite ℚ_[p] K]

instance periodCoefficientAlgebra : Algebra (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p) :=
  (UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K)).toAlgebra

instance periodCoefficientSMul : SMul (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p) :=
  ⟨fun a b => UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) a * b⟩

instance periodCoefficientModule : Module (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p) := Algebra.toModule

instance periodCoefficientDistrib : DistribMulAction (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p) :=
  (periodCoefficientModule p K).toDistribMulAction

instance periodCoefficientAction : MulAction (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p) :=
  (periodCoefficientDistrib p K).toMulAction

instance periodPadicSMul : SMul ℚ_[p] (Logarithm.PeriodRings.BCris p) := (Galois.PeriodStructure.bCris_padicAlgebra p).toSMul

instance periodPadicModule : Module ℚ_[p] (Logarithm.PeriodRings.BCris p) := Galois.PeriodStructure.bCris_padicModule p

instance periodPadicDistrib : DistribMulAction ℚ_[p] (Logarithm.PeriodRings.BCris p) :=
  (periodPadicModule p).toDistribMulAction

instance periodPadicAction : MulAction ℚ_[p] (Logarithm.PeriodRings.BCris p) := (periodPadicDistrib p).toMulAction

instance periodCoefficientTower : IsScalarTower ℚ_[p] (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p) :=
  IsScalarTower.of_algebraMap_eq (R := ℚ_[p]) (S := ResidueCoefficientField.ResidueCoefficient p K) (A := Logarithm.PeriodRings.BCris p)
    (fun a => ((CoefficientComparison.coefficientFieldToBCrisAlg p (FiniteFieldResidue.residueEmbedding p K)).commutes a).symm)

instance periodCoefficientComm : SMulCommClass ℚ_[p] (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p) where
  smul_comm a b x := by
    change Galois.PeriodStructure.padicToBCris p a * (UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) b * x) =
      UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) b * (Galois.PeriodStructure.padicToBCris p a * x)
    ring

instance fieldCoefficientAlgebra : Algebra (ResidueCoefficientField.ResidueCoefficient p K) K :=
  (ResidueCoefficientField.coefficientToK p K).toRingHom.toAlgebra

instance fieldCoefficientModule : Module (ResidueCoefficientField.ResidueCoefficient p K) K := Algebra.toModule

instance fieldCoefficientTower : IsScalarTower ℚ_[p] (ResidueCoefficientField.ResidueCoefficient p K) K :=
  IsScalarTower.of_algebraMap_eq (fun a => ((ResidueCoefficientField.coefficientToK p K).commutes a).symm)

theorem periodRepresentation_coefficient (σ : K.fixingSubgroup) (a : ResidueCoefficientField.ResidueCoefficient p K) (b : Logarithm.PeriodRings.BCris p) :
    Galois.PeriodStructure.periodRepresentation p σ.val (a • b) = a • Galois.PeriodStructure.periodRepresentation p σ.val b := by
  change Galois.galoisBCrisMap p σ.val (UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) a * b) =
    UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) a * Galois.galoisBCrisMap p σ.val b
  rw [map_mul, ResidueCoefficientField.coefficientBCris_fixed]

theorem periodFrobenius_coefficient (a : ResidueCoefficientField.ResidueCoefficient p K) (b : Logarithm.PeriodRings.BCris p) :
    Galois.PeriodStructure.bCrisFrobeniusAlg p (a • b) = UnramifiedCoefficients.coefficientFrobenius (p := p) a • Galois.PeriodStructure.bCrisFrobeniusAlg p b := by
  change Logarithm.bCrisFrobenius p (UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) a * b) =
    UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) (UnramifiedCoefficients.coefficientFrobenius (p := p) a) * Logarithm.bCrisFrobenius p b
  rw [map_mul, UnramifiedCoefficients.coefficientFieldToBCris_frobenius]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

instance tensorCoefficientSMul : SMul (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :=
  TensorProduct.leftHasSMul

instance tensorCoefficientModule : Module (ResidueCoefficientField.ResidueCoefficient p K) (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :=
  TensorProduct.leftModule

instance tensorPadicSMul : SMul ℚ_[p] (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :=
  TensorProduct.leftHasSMul

instance tensorPadicModule : Module ℚ_[p] (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :=
  TensorProduct.leftModule

theorem tensorRepresentation_coefficient (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    (σ : K.fixingSubgroup) (a : ResidueCoefficientField.ResidueCoefficient p K) (x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :
    DcrisD.tensorRepresentation p K ρ σ (a • x) = a • DcrisD.tensorRepresentation p K ρ σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    simp only [DcrisD.tensorRepresentation, Representation.tprod_apply, MonoidHom.comp_apply,
      TensorProduct.smul_tmul', TensorProduct.map_tmul]
    exact congrArg (fun c : Logarithm.PeriodRings.BCris p => c ⊗ₜ[ℚ_[p]] ρ σ v)
      (periodRepresentation_coefficient p K σ a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem coefficient_smul_mem_Dcris (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    (a : ResidueCoefficientField.ResidueCoefficient p K) {x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V} (hx : x ∈ DcrisD.Dcris p K ρ) :
    a • x ∈ DcrisD.Dcris p K ρ := by
  intro σ
  exact (tensorRepresentation_coefficient p K ρ σ a x).trans (congrArg (a • ·) (hx σ))

instance dCrisCoefficientSMul (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    SMul (ResidueCoefficientField.ResidueCoefficient p K) (DcrisD.Dcris p K ρ) :=
  ⟨fun a x => ⟨a • x.val, coefficient_smul_mem_Dcris p K ρ a x.property⟩⟩

instance dCrisCoefficientModule (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Module (ResidueCoefficientField.ResidueCoefficient p K) (DcrisD.Dcris p K ρ) :=
  Subtype.val_injective.module (ResidueCoefficientField.ResidueCoefficient p K) (DcrisD.Dcris p K ρ).subtype.toAddMonoidHom
    (fun _ _ => rfl)

instance dCrisPadicSMul (ρ : Representation ℚ_[p] K.fixingSubgroup V) : SMul ℚ_[p] (DcrisD.Dcris p K ρ) :=
  ⟨fun a x => ⟨a • x.val, (DcrisD.Dcris p K ρ).smul_mem a x.property⟩⟩

instance dCrisCoefficientTower (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    IsScalarTower ℚ_[p] (ResidueCoefficientField.ResidueCoefficient p K) (DcrisD.Dcris p K ρ) where
  smul_assoc a b x := Subtype.ext (smul_assoc a b x.val)

theorem tensorFrobenius_coefficient (a : ResidueCoefficientField.ResidueCoefficient p K) (x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :
    DcrisD.tensorFrobenius p (a • x) = UnramifiedCoefficients.coefficientFrobenius (p := p) a • DcrisD.tensorFrobenius p x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    simp only [TensorProduct.smul_tmul', DcrisD.tensorFrobenius_tmul, periodFrobenius_coefficient]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem dCrisFrobenius_semilinear (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    (a : ResidueCoefficientField.ResidueCoefficient p K) (x : DcrisD.Dcris p K ρ) :
    DcrisD.dCrisFrobenius p K ρ (a • x) = UnramifiedCoefficients.coefficientFrobenius (p := p) a • DcrisD.dCrisFrobenius p K ρ x :=
  Subtype.ext (tensorFrobenius_coefficient p K a x.val)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisCoefficients
