import OAI.Analysis.PDE.Elliptic.Boundary.HolderActions
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ChainRule

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {α : ℝ}

local instance fourthComposeScalar1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeScalar1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeScalar2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeScalar2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeScalar3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeScalar3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeScalar4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeScalar4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeField1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fourthComposeField1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance fourthComposeField2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeField2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeField3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeField3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeField4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeField4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

def holderFourthComposeTerms (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (Q : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (q v w z : E) (i : Fin 15) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  match i.val with
  | 0 => holderAction₄ hα Q (holderEvaluate (J) q) (holderEvaluate (J) v) (holderEvaluate (J) w) (holderEvaluate (J) z)
  | 1 => holderAction₃ hα T (holderEvaluate (holderEvaluate (K) q) v) (holderEvaluate (J) w) (holderEvaluate (J) z)
  | 2 => holderAction₃ hα T (holderEvaluate (J) v) (holderEvaluate (holderEvaluate (K) q) w) (holderEvaluate (J) z)
  | 3 => holderAction₃ hα T (holderEvaluate (J) v) (holderEvaluate (J) w) (holderEvaluate (holderEvaluate (K) q) z)
  | 4 => holderAction₃ hα T (holderEvaluate (J) q) (holderEvaluate (holderEvaluate (K) v) w) (holderEvaluate (J) z)
  | 5 => holderAction₂ hα H (holderEvaluate (holderEvaluate (holderEvaluate (L) q) v) w) (holderEvaluate (J) z)
  | 6 => holderAction₂ hα H (holderEvaluate (holderEvaluate (K) v) w) (holderEvaluate (holderEvaluate (K) q) z)
  | 7 => holderAction₃ hα T (holderEvaluate (J) q) (holderEvaluate (J) w) (holderEvaluate (holderEvaluate (K) v) z)
  | 8 => holderAction₂ hα H (holderEvaluate (holderEvaluate (K) q) w) (holderEvaluate (holderEvaluate (K) v) z)
  | 9 => holderAction₂ hα H (holderEvaluate (J) w) (holderEvaluate (holderEvaluate (holderEvaluate (L) q) v) z)
  | 10 => holderAction₃ hα T (holderEvaluate (J) q) (holderEvaluate (J) v) (holderEvaluate (holderEvaluate (K) w) z)
  | 11 => holderAction₂ hα H (holderEvaluate (holderEvaluate (K) q) v) (holderEvaluate (holderEvaluate (K) w) z)
  | 12 => holderAction₂ hα H (holderEvaluate (J) v) (holderEvaluate (holderEvaluate (holderEvaluate (L) q) w) z)
  | 13 => holderAction₂ hα H (holderEvaluate (J) q) (holderEvaluate (holderEvaluate (holderEvaluate (L) v) w) z)
  | _ => OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D (holderEvaluate (holderEvaluate (holderEvaluate (holderEvaluate (V) q) v) w) z)

def holderFourthComposeComponent (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (Q : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (q v w z : E) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  ∑ i : Fin 15, holderFourthComposeTerms hα D H T Q J K L V q v w z i

omit [FiniteDimensional ℝ E] in
theorem holderFourthComposeTerms_bound (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (Q : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    {R N : ℝ} (hR : 0 ≤ R) (hN : 1 ≤ N)
    (hD : ‖D‖ ≤ R) (hH : ‖H‖ ≤ R) (hT : ‖T‖ ≤ R) (hQ : ‖Q‖ ≤ R)
    (hJ : ‖J‖ ≤ N) (hK : ‖K‖ ≤ N) (hL : ‖L‖ ≤ N) (hV : ‖V‖ ≤ N)
    {q v w z : E} (hq : ‖q‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (i : Fin 15) :
    ‖holderFourthComposeTerms hα D H T Q J K L V q v w z i‖ ≤ (2*N)^4*R := by
  have hN₀ : 0 ≤ N := le_trans zero_le_one hN
  have hj (a : E) (ha : ‖a‖ ≤ 1) : ‖holderEvaluate J a‖ ≤ N :=
    (holderEvaluate_norm_le J ha).trans hJ
  have hk (a b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
      ‖holderEvaluate (holderEvaluate K a) b‖ ≤ N :=
    (holderEvaluate_norm_le _ hb).trans ((holderEvaluate_norm_le K ha).trans hK)
  have hl (a b c : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
      ‖holderEvaluate (holderEvaluate (holderEvaluate L a) b) c‖ ≤ N :=
    (holderEvaluate_norm_le _ hc).trans
      ((holderEvaluate_norm_le _ hb).trans ((holderEvaluate_norm_le L ha).trans hL))
  have hvv (a b c d : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
      ‖holderEvaluate (holderEvaluate (holderEvaluate (holderEvaluate V a) b) c) d‖ ≤ N :=
    (holderEvaluate_norm_le _ hd).trans ((holderEvaluate_norm_le _ hc).trans
      ((holderEvaluate_norm_le _ hb).trans ((holderEvaluate_norm_le V ha).trans hV)))
  have h1 (a : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (ha : ‖a‖ ≤ N) :
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D a‖ ≤ (2*N)^4*R := by
    calc
      _ ≤ 2*R*N := holderAction_bound hα D a hR hN₀ hD ha
      _ = (2*N)^1*R := by ring
      _ ≤ _ := holder_action_power_mono hN hR (by norm_num)
  have h2 (a b : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (ha : ‖a‖ ≤ N) (hb : ‖b‖ ≤ N) :
      ‖holderAction₂ hα H a b‖ ≤ (2*N)^4*R :=
    (holderAction₂_bound hα H a b hR hN₀ hH ha hb).trans
      (holder_action_power_mono hN hR (by norm_num))
  have h3 (a b c : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (ha : ‖a‖ ≤ N) (hb : ‖b‖ ≤ N) (hc : ‖c‖ ≤ N) :
      ‖holderAction₃ hα T a b c‖ ≤ (2*N)^4*R :=
    (holderAction₃_bound hα T a b c hR hN₀ hT ha hb hc).trans
      (holder_action_power_mono hN hR (by norm_num))
  have h4 (a b c d : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (ha : ‖a‖ ≤ N) (hb : ‖b‖ ≤ N) (hc : ‖c‖ ≤ N) (hd : ‖d‖ ≤ N) :
      ‖holderAction₄ hα Q a b c d‖ ≤ (2*N)^4*R :=
    holderAction₄_bound hα Q a b c d hR hN₀ hQ ha hb hc hd
  fin_cases i
  · exact h4 _ _ _ _ (hj q hq) (hj v hv) (hj w hw) (hj z hz)
  · exact h3 _ _ _ (hk q v hq hv) (hj w hw) (hj z hz)
  · exact h3 _ _ _ (hj v hv) (hk q w hq hw) (hj z hz)
  · exact h3 _ _ _ (hj v hv) (hj w hw) (hk q z hq hz)
  · exact h3 _ _ _ (hj q hq) (hk v w hv hw) (hj z hz)
  · exact h2 _ _ (hl q v w hq hv hw) (hj z hz)
  · exact h2 _ _ (hk v w hv hw) (hk q z hq hz)
  · exact h3 _ _ _ (hj q hq) (hj w hw) (hk v z hv hz)
  · exact h2 _ _ (hk q w hq hw) (hk v z hv hz)
  · exact h2 _ _ (hj w hw) (hl q v z hq hv hz)
  · exact h3 _ _ _ (hj q hq) (hj v hv) (hk w z hw hz)
  · exact h2 _ _ (hk q v hq hv) (hk w z hw hz)
  · exact h2 _ _ (hj v hv) (hl q w z hq hw hz)
  · exact h2 _ _ (hj q hq) (hl v w z hv hw hz)
  · exact h1 _ (hvv q v w z hq hv hw hz)

omit [FiniteDimensional ℝ E] in
theorem holderFourthComposeComponent_bound (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (Q : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    {R N : ℝ} (hR : 0 ≤ R) (hN : 1 ≤ N)
    (hD : ‖D‖ ≤ R) (hH : ‖H‖ ≤ R) (hT : ‖T‖ ≤ R) (hQ : ‖Q‖ ≤ R)
    (hJ : ‖J‖ ≤ N) (hK : ‖K‖ ≤ N) (hL : ‖L‖ ≤ N) (hV : ‖V‖ ≤ N)
    {q v w z : E} (hq : ‖q‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖holderFourthComposeComponent hα D H T Q J K L V q v w z‖ ≤ 15*((2*N)^4*R) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 15, (2*N)^4*R := Finset.sum_le_sum (fun i _ =>
      holderFourthComposeTerms_bound hα D H T Q J K L V hR hN hD hH hT hQ hJ hK hL hV hq hv hw hz i)
    _ = _ := by simp


omit [FiniteDimensional ℝ E] in
theorem value_holderFourthComposeComponent (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (Q : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (q v w z : E) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderFourthComposeComponent hα D H T Q J K L V q v w z) x =
      fourthChainValue (OAI.Analysis.Normed.Function.Holder.HolderMap.value D x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value H x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value T x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value L x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value V x) q v w z := by
  change OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM (holderFourthComposeComponent hα D H T Q J K L V q v w z) x = _
  simp [holderFourthComposeComponent, holderFourthComposeTerms, Fin.sum_univ_succ,
    OAI.Analysis.Normed.Function.Holder.HolderMap.value_add, holderAction₂, holderAction₃, holderAction₄, fourthChainValue, add_assoc]


end OAI.Analysis.PDE.Elliptic
