import OAI.Analysis.Normed.Function.Holder.DirichletFourthSourceHolder
import OAI.Analysis.PDE.Dirichlet.Fourth.FieldEquation
import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion

/-! The actual Moore cofactor and its spatial derivative as smooth functions
of the second and third jets, with uniform Hölder bounds on bounded jet sets. -/
noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.Normed.Function.Holder OAI.Analysis.Normed.Function.Holder.HolderMap

local instance coefficientJetCLMGroup (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance coefficientJetCLMSpace (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (E →L[ℝ] F) := inferInstance

variable {n : ℕ}
local notation "E" => CoordinateSpace n 4
local notation "H2" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "H3" => (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
local instance coefficientJetMatrixValueGroup :
    NormedAddCommGroup (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedAddCommGroup ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ))
local instance coefficientJetMatrixValueSpace :
    NormedSpace ℝ (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedSpace ℝ ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ))
local instance coefficientJetFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance coefficientJetFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance coefficientJetSecondGroup : NormedAddCommGroup H2 := inferInstance
local instance coefficientJetSecondSpace : NormedSpace ℝ H2 := inferInstance
local instance coefficientJetThirdGroup : NormedAddCommGroup H3 := inferInstance
local instance coefficientJetThirdSpace : NormedSpace ℝ H3 := inferInstance
local instance coefficientJetMatrixGroup :
    NormedAddCommGroup (E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (E →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))
local instance coefficientJetMatrixSpace :
    NormedSpace ℝ (E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (E →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))
local instance coefficientJetDerivativeGroup :
    NormedAddCommGroup (H2 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (H2 →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))
local instance coefficientJetDerivativeSpace :
    NormedSpace ℝ (H2 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (H2 →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))

def mooreCoefficientJetMap (H : H2) : Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ :=
  mooreRealMatrix (secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots H)

theorem contDiff_mooreCoefficientJetMap (k : WithTop ℕ∞) :
    ContDiff ℝ k (mooreCoefficientJetMap (n := n)) :=
  (contDiff_mooreRealMatrix n k).comp (secondJetToQuaternionCLM (m := n) OAI.Analysis.Calculus.Quaternion.fourSlots).contDiff

@[simp] theorem mooreCoefficientJetMap_actual (u : E → ℝ) (x : E) :
    mooreCoefficientJetMap (fderiv ℝ (fderiv ℝ u) x) =
      mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) := rfl

def mooreCoefficientDerivativeJetMap (q : H2 × H3) :
    E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ :=
  (fderiv ℝ mooreCoefficientJetMap q.1).comp q.2

theorem contDiff_mooreCoefficientDerivativeJetMap (k : WithTop ℕ∞) :
    ContDiff ℝ k (mooreCoefficientDerivativeJetMap (n := n)) := by
  have hd : ContDiff ℝ k (fderiv ℝ (mooreCoefficientJetMap (n := n))) :=
    (contDiff_mooreCoefficientJetMap ⊤).fderiv_right (by simp)
  exact (hd.comp contDiff_fst).clm_comp contDiff_snd

theorem mooreCoefficientDerivativeJetMap_actual (u : E → ℝ) (hu : ContDiff ℝ 3 u) (x : E) :
    mooreCoefficientDerivativeJetMap
      (fderiv ℝ (fderiv ℝ u) x, fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) =
        fderiv ℝ (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) x := by
  have hH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  exact (((contDiff_mooreCoefficientJetMap (n := n) 1).differentiable one_ne_zero _).hasFDerivAt.comp x
    (hH.differentiable one_ne_zero x).hasFDerivAt).fderiv.symm

theorem exists_mooreCoefficient_jet_holder_bound {X : Type*} [MetricSpace X]
    {α R : ℝ} (hα : 0 ≤ α) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X H2 α) (U3 : OAI.Analysis.Normed.Function.Holder.HolderMap X H3 α),
      ‖U2‖ ≤ R → ‖U3‖ ≤ R →
      ∃ (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
        (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = mooreCoefficientJetMap (OAI.Analysis.Normed.Function.Holder.HolderMap.value U2 x)) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = mooreCoefficientDerivativeJetMap (OAI.Analysis.Normed.Function.Holder.HolderMap.value U2 x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U3 x)) ∧
        ‖A‖ ≤ C ∧ ‖DA‖ ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound (X := X)
    (contDiff_mooreCoefficientJetMap (n := n) 1) hα hR
  obtain ⟨C2, hC2, h2⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound (X := X)
    (contDiff_mooreCoefficientDerivativeJetMap (n := n) 1) hα hR
  refine ⟨(C1 + C2) * (1 + R), by positivity, ?_⟩
  intro U2 U3 hU2 hU3
  obtain ⟨A, hA, hAn⟩ := h1 U2 hU2
  obtain ⟨DA, hDA, hDAn⟩ := h2 (OAI.Analysis.Normed.Function.Holder.HolderMap.pair U2 U3) (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hU2 hU3)
  refine ⟨A, DA, hA, ?_, ?_, ?_⟩
  · intro x
    simpa only [OAI.Analysis.Normed.Function.Holder.HolderMap.value_pair] using hDA x
  · exact hAn.trans (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
  · apply hDAn.trans
    exact mul_le_mul (by linarith) (by linarith [OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hU2 hU3])
      (by positivity) (by positivity)

end OAI.Analysis.PDE.Dirichlet
