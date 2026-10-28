import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftCalculus
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance pullFGGroup : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
local instance pullFGSpace : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
local instance pullEGGroup : NormedAddCommGroup (E →L[ℝ] G) := inferInstance
local instance pullEGSpace : NormedSpace ℝ (E →L[ℝ] G) := inferInstance
local instance pullFFGGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance pullFFGSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance pullEEGGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] G) := inferInstance
local instance pullEEGSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] G) := inferInstance
local instance pullEFGGroup : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] G) := inferInstance
local instance pullEFGSpace : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] G) := inferInstance
local instance pullFFFGGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance pullFFFGSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance pullEEEGGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] G) := inferInstance
local instance pullEEEGSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] G) := inferInstance

def precomposeJet (L : E →L[ℝ] F) : (F →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) :=
  (ContinuousLinearMap.compL ℝ E F G).flip L

@[simp] theorem precomposeJet_apply (L : E →L[ℝ] F) (T : F →L[ℝ] G) :
    precomposeJet L T = T.comp L := rfl

theorem norm_precomposeJet_apply (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (T : F →L[ℝ] G) : ‖precomposeJet L T‖ ≤ ‖T‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le T L).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL (norm_nonneg T))

theorem norm_precomposeJet (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    ‖precomposeJet (G := G) L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa only [one_mul] using norm_precomposeJet_apply L hL T

def precomposeSecondJet (L : E →L[ℝ] F) :
    (F →L[ℝ] F →L[ℝ] G) →L[ℝ] (E →L[ℝ] E →L[ℝ] G) :=
  (ContinuousLinearMap.compL ℝ E (F →L[ℝ] G) (E →L[ℝ] G) (precomposeJet L)).comp
    (precomposeJet L)

@[simp] theorem precomposeSecondJet_apply (L : E →L[ℝ] F) (T : F →L[ℝ] F →L[ℝ] G) :
    precomposeSecondJet L T = (precomposeJet L).comp (T.comp L) := rfl

theorem norm_precomposeSecondJet_apply (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (T : F →L[ℝ] F →L[ℝ] G) : ‖precomposeSecondJet L T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖precomposeJet L‖ * ‖T.comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T.comp L‖ := mul_le_mul_of_nonneg_right (norm_precomposeJet L hL) (norm_nonneg _)
    _ ≤ ‖T‖ := by
      rw [one_mul]
      exact (ContinuousLinearMap.opNorm_comp_le T L).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL (norm_nonneg T))

theorem norm_precomposeSecondJet (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    ‖precomposeSecondJet (G := G) L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa only [one_mul] using norm_precomposeSecondJet_apply L hL T

def precomposeThirdJet (L : E →L[ℝ] F) (T : F →L[ℝ] F →L[ℝ] F →L[ℝ] G) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] G := (precomposeSecondJet L).comp (T.comp L)

theorem norm_precomposeThirdJet (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (T : F →L[ℝ] F →L[ℝ] F →L[ℝ] G) : ‖precomposeThirdJet L T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖precomposeSecondJet (G := G) L‖ * ‖T.comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T.comp L‖ := mul_le_mul_of_nonneg_right (norm_precomposeSecondJet L hL) (norm_nonneg _)
    _ ≤ ‖T‖ := by
      rw [one_mul]
      exact (ContinuousLinearMap.opNorm_comp_le T L).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL (norm_nonneg T))

theorem hasFDerivAt_precomposeFirstJet (L : E →L[ℝ] F)
    (D : F → F →L[ℝ] G) (DD : F → F →L[ℝ] F →L[ℝ] G)
    (x : E) (hD : HasFDerivAt D (DD (L x)) (L x)) :
    HasFDerivAt (fun y ↦ precomposeJet L (D (L y))) (precomposeSecondJet L (DD (L x))) x := by
  exact (precomposeJet L).hasFDerivAt.comp x (hD.comp x L.hasFDerivAt)

theorem hasFDerivAt_precomposeSecondJet (L : E →L[ℝ] F)
    (DD : F → F →L[ℝ] F →L[ℝ] G) (DDD : F → F →L[ℝ] F →L[ℝ] F →L[ℝ] G)
    (x : E) (hDD : HasFDerivAt DD (DDD (L x)) (L x)) :
    HasFDerivAt (fun y ↦ precomposeSecondJet L (DD (L y)))
      (precomposeThirdJet L (DDD (L x))) x := by
  exact (precomposeSecondJet L).hasFDerivAt.comp x (hDD.comp x L.hasFDerivAt)

end OAI.Analysis.PDE.Schauder
