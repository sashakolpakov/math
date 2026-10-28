import OAI.Analysis.PDE.Elliptic.Boundary.Third.ChainRule
import OAI.Analysis.PDE.Elliptic.Boundary.CommutatorHolder

/-! Hölder control of the exact third-order coordinate-change formula. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {α : ℝ}

local instance thirdComposeFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdComposeFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdComposeSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdComposeSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdComposeThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdComposeThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdComposeFieldGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance thirdComposeFieldSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance thirdComposeFieldSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance thirdComposeFieldSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance thirdComposeFieldThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance thirdComposeFieldThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

def holderThirdComposeComponent (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (q v w : E) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T
    (holderEvaluate J q)) (holderEvaluate J v)) (holderEvaluate J w) +
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate (holderEvaluate K q) v))
    (holderEvaluate J w) +
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate J v))
    (holderEvaluate (holderEvaluate K q) w) +
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate J q))
    (holderEvaluate (holderEvaluate K v) w) +
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D (holderEvaluate (holderEvaluate (holderEvaluate L q) v) w)

omit [FiniteDimensional ℝ E] in
theorem value_holderThirdComposeComponent (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α) (q v w : E) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderThirdComposeComponent hα D H T J K L q v w) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value T x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x q) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x v) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x q v) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x v) (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x q w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x q) (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x v w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value D x (OAI.Analysis.Normed.Function.Holder.HolderMap.value L x q v w) := rfl

omit [FiniteDimensional ℝ E] in
theorem holderThirdComposeComponent_norm_le (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    {q v w : E} (hq : ‖q‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖holderThirdComposeComponent hα D H T J K L q v w‖ ≤
      8*‖T‖*‖J‖^3 + 12*‖H‖*‖K‖*‖J‖ + 2*‖D‖*‖L‖ := by
  have hpair (a b : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) :
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H a) b‖ ≤ 4*‖H‖*‖a‖*‖b‖ := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
    calc
      _ ≤ 2*(2*‖H‖*‖a‖)*‖b‖ := by
        gcongr
        exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα H a
      _ = _ := by ring
  have htriple (a b c : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) :
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T a) b) c‖ ≤
        8*‖T‖*‖a‖*‖b‖*‖c‖ := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
    calc
      _ ≤ 2*(2*(2*‖T‖*‖a‖)*‖b‖)*‖c‖ := by
        gcongr
        apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
        gcongr
        exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα T a
      _ = _ := by ring
  have hKn (a b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
      ‖holderEvaluate (holderEvaluate K a) b‖ ≤ ‖K‖ :=
    (holderEvaluate_norm_le _ hb).trans (holderEvaluate_norm_le _ ha)
  let a := OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T
    (holderEvaluate J q)) (holderEvaluate J v)) (holderEvaluate J w)
  let b := OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate (holderEvaluate K q) v))
    (holderEvaluate J w)
  let c := OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate J v))
    (holderEvaluate (holderEvaluate K q) w)
  let d := OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate J q))
    (holderEvaluate (holderEvaluate K v) w)
  let e := OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D (holderEvaluate (holderEvaluate (holderEvaluate L q) v) w)
  have ha : ‖a‖ ≤ 8*‖T‖*‖J‖^3 := by
    apply (htriple _ _ _).trans
    calc
      _ ≤ 8*‖T‖*‖J‖*‖J‖*‖J‖ := by
        gcongr
        · exact holderEvaluate_norm_le _ hq
        · exact holderEvaluate_norm_le _ hv
        · exact holderEvaluate_norm_le _ hw
      _ = _ := by ring
  have hb : ‖b‖ ≤ 4*‖H‖*‖K‖*‖J‖ := by
    apply (hpair _ _).trans
    gcongr
    · exact hKn q v hq hv
    · exact holderEvaluate_norm_le _ hw
  have hc : ‖c‖ ≤ 4*‖H‖*‖K‖*‖J‖ := by
    apply (hpair _ _).trans
    calc
      _ ≤ 4*‖H‖*‖J‖*‖K‖ := by
        gcongr
        · exact holderEvaluate_norm_le _ hv
        · exact hKn q w hq hw
      _ = _ := by ring
  have hd : ‖d‖ ≤ 4*‖H‖*‖K‖*‖J‖ := by
    apply (hpair _ _).trans
    calc
      _ ≤ 4*‖H‖*‖J‖*‖K‖ := by
        gcongr
        · exact holderEvaluate_norm_le _ hq
        · exact hKn v w hv hw
      _ = _ := by ring
  have he : ‖e‖ ≤ 2*‖D‖*‖L‖ := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (holderEvaluate_norm_le _ hw).trans
      ((holderEvaluate_norm_le _ hv).trans (holderEvaluate_norm_le _ hq))
  change ‖a+b+c+d+e‖ ≤ _
  linarith [norm_add_le a b, norm_add_le (a+b) c, norm_add_le (a+b+c) d,
    norm_add_le (a+b+c+d) e]

omit [FiniteDimensional ℝ E] in
theorem holderThirdComposeComponent_value_actual
    {S : Set E} (hα : 0 ≤ α) {u : E → ℝ} {G : E → E}
    (hu : ContDiff ℝ 3 u) (hG : ContDiff ℝ 3 G)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (hD : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u (G x))
    (hH : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) (G x))
    (hT : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (G x))
    (hJ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ G x)
    (hK : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ G) x)
    (hL : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value L x = fderiv ℝ (fderiv ℝ (fderiv ℝ G)) x)
    (q v w : E) (x : S) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderThirdComposeComponent hα D H T J K L q v w) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)))) x q v w := by
  rw [value_holderThirdComposeComponent, hD, hH, hT, hJ, hK, hL]
  exact (third_fderiv_comp hu.contDiffAt hG.contDiffAt q v w).symm

end OAI.Analysis.PDE.Elliptic
