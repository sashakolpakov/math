import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorNilpotentDevissage
import Mathlib.RingTheory.Flat.Stability

/-! # Maximal Ideal Flat Reduction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MaximalIdealFlatReduction

noncomputable section

/-! Reduction of a base-changed module by an extended maximal ideal
is flat over the reduced coefficient ring, by scalar extension from
the old residue field. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B] (A : Type v) [CommRing A] [Algebra B A]
variable (M : Type w) [AddCommGroup M] [Module B M]

theorem extendedMaximalIdeal_reduction_flat (I : Ideal B) [I.IsMaximal] :
    Module.Flat (A ⧸ I.map (algebraMap B A))
      ((A ⧸ I.map (algebraMap B A)) ⊗[A] (A ⊗[B] M)) := by
  let k := B ⧸ I
  let C := A ⧸ I.map (algebraMap B A)
  let : Field k := Ideal.Quotient.field I
  let : Algebra k C := Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
    I ≤ (I.map (algebraMap B A)).comap (algebraMap B A))
  let : IsScalarTower B k C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Flat k (k ⊗[B] M) := inferInstance
  have : Module.Flat C (C ⊗[k] (k ⊗[B] M)) := inferInstance
  have : Module.Flat C (C ⊗[B] M) := Module.Flat.of_linearEquiv
    (AlgebraTensorModule.cancelBaseChange B k C C M).symm
  exact Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange B A C C M)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MaximalIdealFlatReduction
