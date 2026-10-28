import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConormalEigenquotient
import Mathlib.RingTheory.Unramified.Finite

/-! # Unramified Character Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnramifiedCharacterQuotient

noncomputable section

/-! Character quotients of finite projective modules over a finite-type
unramified algebra are direct summands over the base. The splitting is
constructed from the algebra's proved separability element. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConormalEigenquotient

variable {R B V : Type} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup V] [Module R V]

def characterTensorEvaluation (χ : B →ₐ[R] R) : B ⊗[R] V →ₗ[R] V :=
  (TensorProduct.lid R V).toLinearMap.comp (χ.toLinearMap.rTensor V)

@[simp] theorem characterTensorEvaluation_tmul (χ : B →ₐ[R] R) (b : B) (v : V) :
    characterTensorEvaluation χ (b ⊗ₜ[R] v) = χ b • v := rfl

theorem characterTensorEvaluation_smul (χ : B →ₐ[R] R) (b : B) (t : B ⊗[R] V) :
    characterTensorEvaluation χ (b • t) = χ b • characterTensorEvaluation χ t := by
  induction t using TensorProduct.inductionOn with
  | tmul a v => simp [TensorProduct.smul_tmul', map_mul, mul_smul]
  | add t u ht hu => simp only [smul_add, map_add, ht, hu]

variable [Module B V] [IsScalarTower R B V]

def characterActionRelations (χ : B →ₐ[R] R) : Submodule R V :=
  PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenRelations (Algebra.lsmul R R V : B →ₐ[R] Module.End R V) χ

theorem characterActionRelations_mkQ_smul (χ : B →ₐ[R] R) (b : B) (v : V) :
    (characterActionRelations χ).mkQ (b • v) =
      (characterActionRelations χ).mkQ (χ b • v) := by
  apply (Submodule.Quotient.eq _).mpr
  have hb : ((Algebra.lsmul R R V) b - χ b • (LinearMap.id : Module.End R V)).range ≤
      characterActionRelations (V := V) χ :=
    le_iSup (fun a : B =>
      ((Algebra.lsmul R R V) a - χ a • (LinearMap.id : Module.End R V)).range) b
  exact hb ⟨v, rfl⟩

def characterTensorMultiplication : B ⊗[R] V →ₗ[R] V :=
  TensorProduct.lift (Algebra.lsmul R R V : B →ₐ[R] Module.End R V).toLinearMap

@[simp] theorem characterTensorMultiplication_tmul (b : B) (v : V) :
    characterTensorMultiplication (b ⊗ₜ[R] v) = b • v := rfl

theorem characterTensorEvaluation_class (χ : B →ₐ[R] R) (t : B ⊗[R] V) :
    (characterActionRelations χ).mkQ (characterTensorEvaluation χ t) =
      (characterActionRelations χ).mkQ (characterTensorMultiplication t) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => exact (characterActionRelations_mkQ_smul χ b v).symm
  | add t u ht hu => simp only [map_add, ht, hu]

variable [Algebra.FormallyUnramified R B] [Algebra.EssFiniteType R B]

def characterProjector (χ : B →ₐ[R] R) : Module.End R V :=
  (characterTensorEvaluation χ).comp ((Algebra.FormallyUnramified.sec R B V).restrictScalars R)

theorem characterProjector_smul (χ : B →ₐ[R] R) (b : B) (v : V) :
    characterProjector χ (b • v) = χ b • characterProjector χ v := by
  change characterTensorEvaluation χ (Algebra.FormallyUnramified.sec R B V (b • v)) = _
  rw [map_smul, characterTensorEvaluation_smul]
  rfl

theorem characterProjector_class (χ : B →ₐ[R] R) (v : V) :
    (characterActionRelations χ).mkQ (characterProjector χ v) =
      (characterActionRelations χ).mkQ v := by
  apply (characterTensorEvaluation_class χ (Algebra.FormallyUnramified.sec R B V v)).trans
  apply congrArg (characterActionRelations χ).mkQ
  exact LinearMap.congr_fun (Algebra.FormallyUnramified.comp_sec R B V) v

theorem characterActionRelations_le_projector_ker (χ : B →ₐ[R] R) :
    characterActionRelations (V := V) χ ≤ (characterProjector χ).ker := by
  change (⨆ b : B, ((Algebra.lsmul R R V) b - χ b • LinearMap.id).range) ≤ _
  apply iSup_le
  intro b v hv
  obtain ⟨w, rfl⟩ := hv
  change characterProjector χ (b • w - χ b • w) = 0
  rw [map_sub, characterProjector_smul, map_smul, sub_self]

def characterQuotientSection (χ : B →ₐ[R] R) :
    V ⧸ characterActionRelations (V := V) χ →ₗ[R] V :=
  (characterActionRelations χ).liftQ (characterProjector χ)
    (characterActionRelations_le_projector_ker χ)

theorem characterQuotientSection_splits (χ : B →ₐ[R] R) :
    (characterActionRelations (V := V) χ).mkQ.comp (characterQuotientSection χ) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := (characterActionRelations χ).mkQ_surjective q
  exact characterProjector_class χ v

theorem characterQuotient_projective [Module.Projective R V] (χ : B →ₐ[R] R) :
    Module.Projective R (V ⧸ characterActionRelations (V := V) χ) :=
  Module.Projective.of_split (characterQuotientSection χ) (characterActionRelations χ).mkQ
    (characterQuotientSection_splits χ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnramifiedCharacterQuotient
