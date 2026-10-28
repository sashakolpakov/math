import OAI.Analysis.Normed.Function.Sobolev.Reflection.Derivative
import OAI.Analysis.Normed.Function.Sobolev.Reflection.Support
import OAI.Analysis.Normed.Function.Sobolev.Reflection.Coefficients

open Set Filter _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

variable {d : ℕ}

def reflectionFamilyWeight (N : ℕ) (k : Fin d) (α : List (Fin d)) (j : Fin N) : ℝ :=
  reflectionCoefficient N j * reflectionNode j ^ α.count k

theorem reflectionFamilyWeight_cons (N : ℕ) (k i : Fin d) (α : List (Fin d)) (j : Fin N) :
    reflectionFamilyWeight N k (i :: α) j =
      reflectionFamilyWeight N k α j * (if i = k then reflectionNode j else 1) := by
  by_cases hi : i = k
  · subst i
    simp [reflectionFamilyWeight,pow_succ,mul_assoc]
  · simp [reflectionFamilyWeight,hi]

theorem reflectionFamilyWeight_sum {N : ℕ} (k : Fin d) (α : List (Fin d))
    (hα : α.length < N) : ∑j, reflectionFamilyWeight N k α j = 1 := by
  apply reflectionCoefficient_moment
  exact lt_of_le_of_lt List.count_le_length hα

def reflectedDerivativeFamily (N : ℕ) (k : Fin d)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ) (α : List (Fin d)) : (Fin d → ℝ) → ℝ :=
  reflectionExtension k reflectionNode (reflectionFamilyWeight N k α) (U α)

theorem reflectedDerivativeFamily_eq (N : ℕ) (k : Fin d)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ) (α : List (Fin d))
    {x : Fin d → ℝ} (hx : 0 < x k) : reflectedDerivativeFamily N k U α x = U α x :=
  reflectionExtension_eq k _ _ _ hx

theorem reflectedDerivativeFamily_memLp (N : ℕ) (k : Fin d)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ) (α : List (Fin d))
    (hU : MemLp (U α) 2) : MemLp (reflectedDerivativeFamily N k U α) 2 :=
  memLp_reflectionExtension k _ _ (fun j ↦ (reflectionNode_negative j).ne) hU

theorem reflectedDerivativeFamily_zero_off (N : ℕ) (k : Fin d)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ) (α : List (Fin d))
    {K : Set (Fin d → ℝ)} (hU : ∀ᵐx, x ∉ K → U α x = 0) :
    ∀ᵐx, x ∉ reflectedSupport k (@reflectionNode N) K →
      reflectedDerivativeFamily N k U α x = 0 :=
  reflectionExtension_zero_off k _ _ (fun j ↦ (reflectionNode_negative j).ne) hU

theorem reflectedDerivativeFamily_weakDerivative (N : ℕ) (k i : Fin d)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ) (α : List (Fin d))
    (hα : α.length < N) (hUi : Integrable (U α)) (hVi : Integrable (U (i :: α)))
    (hD : OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn volume {x | 0 < x k}
      (Pi.single i 1) (U α) (U (i :: α))) :
    OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (Pi.single i 1)
      (reflectedDerivativeFamily N k U α) (reflectedDerivativeFamily N k U (i :: α)) := by
  have h := hasWeakDirectionalDerivative_reflection k i reflectionNode
    (reflectionFamilyWeight N k α) reflectionNode_negative
    (fun _ ↦ reflectionFamilyWeight_sum k α hα) hUi hVi hD
  have hw : (fun j ↦ reflectionFamilyWeight N k α j *
      (if i = k then reflectionNode j else 1)) = reflectionFamilyWeight N k (i :: α) := by
    funext j
    exact (reflectionFamilyWeight_cons N k i α j).symm
  rw [hw] at h
  exact h

end OAI.Analysis.Normed.Function.Sobolev
