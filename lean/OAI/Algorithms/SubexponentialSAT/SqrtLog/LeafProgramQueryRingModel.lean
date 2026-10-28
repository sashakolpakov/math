import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBanked

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open LeafParametersProgram

theorem ring_precision_pos (x : Input) (l : Fin 8 → ℕ) (hg : Guard x) :
    0 < (Execute.guardedModel x l).val 33 := by
  rw [Execute.guardedModel_precision x l (Nat.ne_of_gt hg.2.2.1)]
  exact produce_t_pos x

theorem ring_degree_pos (x : Input) (l : Fin 8 → ℕ) (hg : Guard x) :
    0 < (Execute.guardedModel x l).val 34 := by
  have hq : (produce x).Q≠0 := by have := hg.2.2.2.2.2.2.1; omega
  rw [Execute.guardedModel_degree x l hq]
  exact produce_d_pos x

theorem ring_exponent (x : Input) (l : Fin 8 → ℕ) (hg : Guard x) :
    (Circuit.result Serialization.code (Execute.guardedModel x l)).val 44=
      3^((Execute.guardedModel x l).val 34)-2 := by
  have hq : (produce x).Q≠0 := by have := hg.2.2.2.2.2.2.1; omega
  have hf : (Execute.guardedModel x l).val 35=fieldCard x :=
    (Execute.guardedModel_public x l 10).trans (Layout.model_fieldCard x l hq)
  rw [(Serialization.values _).1,hf,Execute.guardedModel_degree x l hq]
  rfl

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
