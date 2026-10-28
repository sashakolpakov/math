import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ExactEuler
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Cochain Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.CochainEuler

noncomputable section

/-! A bounded exact coherent complex has zero alternating Euler characteristic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem proper_coherent_cochain_kernel_euler
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ Spec (.of k)) [IsProper p] (C : CochainComplex X.Modules ℤ)
    (hC : C.Acyclic) [∀ i, (C.X i).IsQuasicoherent] [∀ i, (C.X i).IsFiniteType] (i : ℤ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X i) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d i (i + 1))) +
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d (i + 1) ((i + 1) + 1))) := by
  have hS : (C.sc' i (i + 1) ((i + 1) + 1)).Exact :=
    ShortComplex.exact_of_iso
      (C.isoSc' i (i + 1) ((i + 1) + 1) (by simp) (by simp)) (hC (i + 1))
  exact @Bounded.ExactEuler.proper_coherent_exact_kernel_euler k _ X _ p _ (C.sc' i (i + 1) ((i + 1) + 1)) hS
    (inferInstance : (C.X i).IsQuasicoherent)
    (inferInstance : (C.X (i + 1)).IsQuasicoherent)
    (inferInstance : (C.X ((i + 1) + 1)).IsQuasicoherent)
    (inferInstance : (C.X i).IsFiniteType)
    (inferInstance : (C.X (i + 1)).IsFiniteType)

theorem proper_coherent_acyclic_euler_sum
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ Spec (.of k)) [IsProper p] (C : CochainComplex X.Modules ℤ)
    (hC : C.Acyclic) [∀ i, (C.X i).IsQuasicoherent] [∀ i, (C.X i).IsFiniteType]
    (r : ℕ) (hpos : IsZero (C.X 1)) (hneg : IsZero (C.X (-(r : ℤ) - 1))) :
    (∑ n ∈ Finset.range (r + 1),
      (-1 : ℤ) ^ n * CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ)))) = 0 := by
  let a : ℕ → ℤ := fun n => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ)))
  let b : ℕ → ℤ := fun n =>
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d (-(n : ℤ)) (-(n : ℤ) + 1)))
  have hzero : a 0 = b 0 := by
    have h := proper_coherent_cochain_kernel_euler p C hC 0
    have hz := Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p (kernel (C.d 1 2))
      (Bounded.ExactEuler.kernel_isZero_of_source_isZero (C.d 1 2) hpos)
    simpa [a, b, hz] using h
  have hstep (n : ℕ) : a (n + 1) = b (n + 1) + b n := by
    let j : ℤ := -((n + 1 : ℕ) : ℤ)
    have hj : j + 1 = -(n : ℤ) := by dsimp [j]; omega
    have h := proper_coherent_cochain_kernel_euler p C hC j
    change a (n + 1) = b (n + 1) +
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d (j + 1) ((j + 1) + 1))) at h
    exact h.trans (congrArg (fun w : ℤ => b (n + 1) + w)
      (congrArg (fun i : ℤ => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d i (i + 1)))) hj))
  have hS : (C.sc' (-(r : ℤ) - 1) (-(r : ℤ)) (-(r : ℤ) + 1)).Exact :=
    ShortComplex.exact_of_iso
      (C.isoSc' (-(r : ℤ) - 1) (-(r : ℤ)) (-(r : ℤ) + 1)
        (by simp) (by simp)) (hC (-(r : ℤ)))
  have hb : b r = 0 := Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _
    (Bounded.ExactEuler.exact_kernel_isZero_of_first_isZero _ hS hneg)
  have h := Bounded.ExactEuler.alternating_sum_of_adjacent_balance a b hzero hstep r
  simpa only [a, hb, mul_zero] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.CochainEuler
