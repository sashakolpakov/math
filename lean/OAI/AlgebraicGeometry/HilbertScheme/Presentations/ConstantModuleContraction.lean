import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Contraction
import Mathlib.Algebra.Module.Basic

/-! # Constant Module Contraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ConstantModuleContraction.ProjectiveCech

/-! The finite subset Čech contraction with values in an arbitrary coefficient module. -/

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]

def constantModuleDifferential (f : Finset σ → M) (s : Finset σ) : M :=
  ∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i • f (s.erase i)

def constantModuleContraction (j : σ) (f : Finset σ → M) (s : Finset σ) : M :=
  if j ∈ s then 0 else Cech.Signs.ProjectiveCech.alternatingSign R s j • f (insert j s)

theorem constantModuleDifferential_contraction_of_mem (j : σ) (f : Finset σ → M)
    (s : Finset σ) (hj : j ∈ s) :
    constantModuleDifferential R M (constantModuleContraction R M j f) s = f s := by
  unfold constantModuleDifferential
  rw [Finset.sum_eq_single j]
  · simp only [constantModuleContraction, Finset.notMem_erase, ↓reduceIte, Finset.insert_erase hj,
      Cech.Signs.ProjectiveCech.alternatingSign_erase_self, smul_smul, Cech.Signs.ProjectiveCech.alternatingSign_square, one_smul]
  · intro i _ hij
    have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    simp only [constantModuleContraction, ite_eq_left hj', smul_zero]
  · exact fun h => (h hj).elim

theorem constantModuleContraction_differential_of_notMem (j : σ) (f : Finset σ → M)
    (s : Finset σ) (hj : j ∉ s) :
    constantModuleContraction R M j (constantModuleDifferential R M f) s =
      f s - constantModuleDifferential R M (constantModuleContraction R M j f) s := by
  rw [constantModuleContraction, ite_eq_right hj, constantModuleDifferential, Finset.sum_insert hj, smul_add]
  have hfirst : Cech.Signs.ProjectiveCech.alternatingSign R s j •
      (Cech.Signs.ProjectiveCech.alternatingSign R (insert j s) j • f ((insert j s).erase j)) = f s := by
    rw [Cech.Signs.ProjectiveCech.alternatingSign_insert_self, Finset.erase_insert hj, smul_smul,
      Cech.Signs.ProjectiveCech.alternatingSign_square, one_smul]
  rw [hfirst, sub_eq_add_neg]
  congr 1
  rw [Finset.smul_sum, constantModuleDifferential, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  have hjs : j ∉ s.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  rw [constantModuleContraction, ite_eq_right hjs, smul_smul, Cech.Signs.ProjectiveCech.alternatingSign_insert_erase R hi hj]
  rw [Finset.erase_insert_of_ne hji, neg_smul, smul_smul]

theorem constantModule_contraction_identity (j : σ) (f : Finset σ → M) (s : Finset σ) :
    constantModuleDifferential R M (constantModuleContraction R M j f) s +
      constantModuleContraction R M j (constantModuleDifferential R M f) s = f s := by
  by_cases hj : j ∈ s
  · rw [constantModuleDifferential_contraction_of_mem R M j f s hj,
      constantModuleContraction, ite_eq_left hj, add_zero]
  · rw [constantModuleContraction_differential_of_notMem R M j f s hj]
    abel

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ConstantModuleContraction.ProjectiveCech
