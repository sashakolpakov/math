import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoefficientCommonExtension
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.MaximalIdealDescent

/-! # Chart Obstruction Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ChartObstructionDescent

noncomputable section

/-! A single finite coefficient algebra kills the residue obstructions
for every algebra in a finite affine cover, universally after further extension. -/

open TensorProduct

universe u v w t z
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]
variable {κ : Type t} [Fintype κ]
variable (S : κ → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable [∀ i, IsNoetherianRing (S i)] [∀ i, Module.Flat A (A ⊗[B] S i)]

theorem finite_coefficient_chart_obstructions_descent
    (C : Subalgebra B A) [Algebra.FiniteType B C] (I : Ideal B) (hI : I.FG) :
    ∃ E : Subalgebra B A, C ≤ E ∧ Algebra.FiniteType B E ∧
      ∀ i (x : (IdealTensor.Obstruction.idealTensorMultiplication B B (S i) I).ker),
        IdealTensor.BaseChange.idealTensorBaseChangeMap B E (S i) I x.val = 0 := by
  classical
  choose D _ hD hz using fun i =>
    ObstructionModuleDescent.idealTensorObstruction_finite_coefficient_descent (S i) (S i) C I hI
  obtain ⟨E, hCE, hE, hDE⟩ := CoefficientCommonExtension.finite_coefficient_common_extension C D hD
  refine ⟨E, hCE, hE, fun i x => ?_⟩
  let : Algebra (D i) E := (Subalgebra.inclusion (hDE i)).toRingHom.toAlgebra
  let : IsScalarTower B (D i) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IdealTensor.Tower.idealTensorBaseChange_zero_of_tower B (D i) E (S i) I x.val
    (hz i ⟨x.val, x.property⟩)

theorem finite_coefficient_chart_universal_injectivity
    (C : Subalgebra B A) [Algebra.FiniteType B C]
    (I : Ideal B) [I.IsMaximal] (hI : I.FG) :
    ∃ E : Subalgebra B A, C ≤ E ∧ Algebra.FiniteType B E ∧
      ∀ (R : Type z) [CommRing R] [Algebra E R] [Algebra B R] [IsScalarTower B E R],
        ∀ i, Function.Injective
          (IdealTensor.Obstruction.idealTensorMultiplication R R (R ⊗[B] S i) (I.map (algebraMap B R))) := by
  obtain ⟨E, hCE, hE, hz⟩ := finite_coefficient_chart_obstructions_descent S C I hI
  refine ⟨E, hCE, hE, ?_⟩
  intro R _ _ _ _ i
  apply IdealObstructionBaseChange.baseChange_maximalIdeal_injective_of_obstructions_zero R I
  intro x
  exact IdealTensor.Tower.idealTensorBaseChange_zero_of_tower B E R (S i) I x.val (hz i x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ChartObstructionDescent
