import OAI.Analysis.PDE.Dirichlet.Linearized

/-! Strict positivity of the real rank-one symbol of the quaternionic linearization. -/

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

theorem quaternion_re_sum {ι : Type*} (s : Finset ι) (f : ι → Quaternion ℝ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem quaternion_re_mul_comm (a b : Quaternion ℝ) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

theorem quaternionRealTrace_outer {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (g : Fin n → Quaternion ℝ) :
    (∑ i, ((C * OAI.Analysis.Calculus.Quaternion.outer g) i i).re) = (quaternionForm C g).re := by
  simp only [Matrix.mul_apply, OAI.Analysis.Calculus.Quaternion.outer, quaternionForm, quaternion_re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [mul_assoc] using quaternion_re_mul_comm (C i j * g j) (star (g i))

theorem mooreDifferential_outer_pos {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (g : Fin n → Quaternion ℝ)
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (hg : g ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer g) := by
  have hC := OAI.LinearAlgebra.Moore.complexify_inverse_posDef n A C hA hAC
  have hq := (OAI.LinearAlgebra.Moore.complexify_posDef_iff (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hC.isHermitian)).mp hC g hg
  rw [OAI.LinearAlgebra.Moore.mooreDifferential_inverse n A (OAI.Analysis.Calculus.Quaternion.outer g) C (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hA.isHermitian)
    (OAI.Analysis.Calculus.Quaternion.outer_isHermitian g) hAC hCA, quaternionRealTrace_outer]
  exact mul_pos hdet hq

theorem moore_principalSymbol_pos {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : Function.Injective (OAI.Analysis.Calculus.Quaternion.gradientMap (m := Fin n) e))
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (ξ : Fin n × Fin s → ℝ) (hξ : ξ ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap e (fun i j ↦ ξ i * ξ j)) := by
  rw [OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne]
  apply mooreDifferential_outer_pos A C _ hA hAC hCA hdet
  intro hg
  apply hξ
  apply he
  rw [hg]
  funext a
  simp [OAI.Analysis.Calculus.Quaternion.gradientMap]

/-- The real principal symbol is strictly positive in every nonzero four-slot direction. -/
theorem moore_fourSlot_principalSymbol_pos {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (ξ : Fin n × Fin 4 → ℝ) (hξ : ξ ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j ↦ ξ i * ξ j)) :=
  moore_principalSymbol_pos OAI.Analysis.Calculus.Quaternion.fourSlots OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots_injective A C hA hAC hCA hdet ξ hξ

/-- The same strict ellipticity holds for the original three-slot Hessian. -/
theorem moore_threeSlot_principalSymbol_pos {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (ξ : Fin n × Fin 3 → ℝ) (hξ : ξ ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.threeSlots (fun i j ↦ ξ i * ξ j)) :=
  moore_principalSymbol_pos OAI.Analysis.Calculus.Quaternion.threeSlots OAI.Analysis.Calculus.Quaternion.gradientMap_threeSlots_injective A C hA hAC hCA hdet ξ hξ

end OAI.Analysis.PDE.Dirichlet
