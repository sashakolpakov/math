import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.CochainEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType

/-! # Exact Cochain Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ExactCochainEuler

noncomputable section

/-! For a coherent complex exact in negative degrees and bounded on
the left, the alternating Euler sum is the Euler characteristic of its
actual final cokernel. This leaves its multiplicities intact. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem alternating_sum_of_adjacent_balance_with_constant (a b : ℕ → ℤ) (c : ℤ)
    (hzero : a 0 = c + b 0) (hstep : ∀ n, a (n + 1) = b (n + 1) + b n) (r : ℕ) :
    (∑ n ∈ Finset.range (r + 1), (-1 : ℤ) ^ n * a n) = c + (-1 : ℤ) ^ r * b r := by
  induction r with
  | zero => simpa using hzero
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, hstep r, pow_succ]
    ring

theorem proper_coherent_negative_exact_euler_sum
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ Spec (.of k)) [IsProper p] (C : CochainComplex X.Modules ℤ)
    (hC : ∀ i : ℤ, i < 0 → C.ExactAt i)
    [∀ i, (C.X i).IsQuasicoherent] [∀ i, (C.X i).IsFiniteType]
    (r : ℕ) (hr : 0 < r) (hneg : IsZero (C.X (-(r : ℤ) - 1))) :
    (∑ n ∈ Finset.range (r + 1), (-1 : ℤ) ^ n * CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ)))) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (cokernel (C.d (-1) 0)) := by
  let d := C.d (-1) 0
  let Q := cokernel d
  let π := cokernel.π d
  have : Q.IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel d
  have : Q.IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType d
  have : (kernel π).IsQuasicoherent := Quasicoherent.Kernels.module_quasicoherent_kernel π
  have : (kernel π).IsFiniteType := Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType π
  let a : ℕ → ℤ := fun n => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ)))
  let b : ℕ → ℤ := fun n => if n = 0 then CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel π)
    else CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d (-(n : ℤ)) (-(n : ℤ) + 1)))
  have hzero : a 0 = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p Q + b 0 := by
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := ⟨ShortComplex.kernelSequence_exact π⟩
    have h := Proper.CohomologyEulerAdditivity.proper_coherent_euler_additive p hS
    change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X 0) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel π) + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p Q at h
    simpa only [a, b, Nat.cast_zero, neg_zero, ite_eq_left rfl, add_comm] using h
  have hstep (n : ℕ) : a (n + 1) = b (n + 1) + b n := by
    by_cases hn : n = 0
    · subst n
      let S := ShortComplex.mk d π (cokernel.condition d)
      have h := Bounded.ExactEuler.proper_coherent_exact_kernel_euler p S (ShortComplex.cokernelSequence_exact d)
      change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-1)) =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d (-1) 0)) +
          CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel π) at h
      simpa [a, b, d] using h
    · let j : ℤ := -((n + 1 : ℕ) : ℤ)
      have hj : j + 1 = -(n : ℤ) := by dsimp [j]; omega
      have hm : j + 1 < 0 := by rw [hj]; omega
      have hS : (C.sc' j (j + 1) ((j + 1) + 1)).Exact :=
        ShortComplex.exact_of_iso (C.isoSc' j (j + 1) ((j + 1) + 1) (by simp) (by simp))
          (hC (j + 1) hm)
      have h := @Bounded.ExactEuler.proper_coherent_exact_kernel_euler k _ X _ p _
        (C.sc' j (j + 1) ((j + 1) + 1)) hS
        (inferInstance : (C.X j).IsQuasicoherent)
        (inferInstance : (C.X (j + 1)).IsQuasicoherent)
        (inferInstance : (C.X ((j + 1) + 1)).IsQuasicoherent)
        (inferInstance : (C.X j).IsFiniteType)
        (inferInstance : (C.X (j + 1)).IsFiniteType)
      change a (n + 1) = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d j (j + 1))) +
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d (j + 1) ((j + 1) + 1))) at h
      dsimp only [b]
      rw [ite_eq_right hn, ite_eq_right (Nat.succ_ne_zero n)]
      exact h.trans (congrArg (fun w : ℤ => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
          (kernel (C.d j (j + 1))) + w)
        (congrArg (fun i : ℤ => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel (C.d i (i + 1)))) hj))
  have hS : (C.sc' (-(r : ℤ) - 1) (-(r : ℤ)) (-(r : ℤ) + 1)).Exact :=
    ShortComplex.exact_of_iso
      (C.isoSc' (-(r : ℤ) - 1) (-(r : ℤ)) (-(r : ℤ) + 1) (by simp) (by simp))
      (hC (-(r : ℤ)) (by omega))
  have hb : b r = 0 := by
    dsimp only [b]
    rw [ite_eq_right (Nat.ne_of_gt hr)]
    exact Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _
      (Bounded.ExactEuler.exact_kernel_isZero_of_first_isZero _ hS hneg)
  have h := alternating_sum_of_adjacent_balance_with_constant a b
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p Q) hzero hstep r
  simpa only [a, hb, mul_zero, add_zero] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ExactCochainEuler
