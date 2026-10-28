import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ObstructionModuleDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealObstructionBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Tower

/-! # Maximal Ideal Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.MaximalIdealDescent

noncomputable section

/-! One finite coefficient algebra makes the extended maximal-ideal
multiplication map injective after every subsequent coefficient extension. -/

open TensorProduct

universe u v w t z
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]
variable (S : Type w) [CommRing S] [Algebra B S] [IsNoetherianRing S]
variable (M : Type t) [AddCommGroup M] [Module B M] [Module S M] [IsScalarTower B S M]
variable [Module.Finite S M] [Module.Flat A (A ⊗[B] M)]

include S in
theorem finite_coefficient_maximalIdeal_universal_injectivity
    (C : Subalgebra B A) [Algebra.FiniteType B C]
    (I : Ideal B) [I.IsMaximal] (hI : I.FG) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      ∀ (R : Type z) [CommRing R] [Algebra D R] [Algebra B R] [IsScalarTower B D R],
        Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication R R (R ⊗[B] M) (I.map (algebraMap B R))) := by
  obtain ⟨D, hCD, hD, hz⟩ := ObstructionModuleDescent.idealTensorObstruction_finite_coefficient_descent S M C I hI
  refine ⟨D, hCD, hD, ?_⟩
  intro R _ _ _ _
  apply IdealObstructionBaseChange.baseChange_maximalIdeal_injective_of_obstructions_zero R I
  intro x
  exact IdealTensor.Tower.idealTensorBaseChange_zero_of_tower B D R M I x.val (hz ⟨x.val, x.property⟩)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.MaximalIdealDescent
