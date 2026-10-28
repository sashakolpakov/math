import OAI.Analysis.PDE.Dirichlet.Fourth.SourceExpression

/-! Uniform bounds for the twice-tangential source from bounded lower jets. -/
noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Normed.Function.Holder.HolderMap

variable {I X : Type} [Fintype I] [DecidableEq I] [MetricSpace X] {α : ℝ}
local notation "E" => EuclideanSpace ℝ I
local instance sourceBoundMatrixValueGroup : NormedAddCommGroup (Matrix I I ℝ) :=
  inferInstanceAs (NormedAddCommGroup (I → I → ℝ))
local instance sourceBoundMatrixValueSpace : NormedSpace ℝ (Matrix I I ℝ) :=
  inferInstanceAs (NormedSpace ℝ (I → I → ℝ))
local instance sourceBoundScalar1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundScalar1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundScalar2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundScalar2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundScalar3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundScalar3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundVector1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance sourceBoundVector1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance sourceBoundVector2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceBoundVector2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceBoundVector3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceBoundVector3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceBoundMatrixGroup : NormedAddCommGroup (E →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (NormedAddCommGroup (E →L[ℝ] (I → I → ℝ)))
local instance sourceBoundMatrixSpace : NormedSpace ℝ (E →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (NormedSpace ℝ (E →L[ℝ] (I → I → ℝ)))
local instance sourceBoundFirstGroup : NormedAddCommGroup (FirstFieldJet I) := by
  unfold FirstFieldJet
  infer_instance
local instance sourceBoundFirstSpace : NormedSpace ℝ (FirstFieldJet I) := by
  unfold FirstFieldJet
  infer_instance
local instance sourceBoundRestGroup : NormedAddCommGroup (SecondFieldRestJet I) := by
  unfold SecondFieldRestJet
  infer_instance
local instance sourceBoundRestSpace : NormedSpace ℝ (SecondFieldRestJet I) := by
  unfold SecondFieldRestJet
  infer_instance
local instance sourceBoundFullGroup : NormedAddCommGroup (SecondFieldSourceJet I) := inferInstance
local instance sourceBoundFullSpace : NormedSpace ℝ (SecondFieldSourceJet I) := inferInstance
local instance sourceBoundScalar1Proper : ProperSpace (E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundScalar2Proper : ProperSpace (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundScalar3Proper : ProperSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceBoundVector1Proper : ProperSpace (E →L[ℝ] E) := inferInstance
local instance sourceBoundVector2Proper : ProperSpace (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceBoundMatrixProper : ProperSpace (E →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (ProperSpace (E →L[ℝ] (I → I → ℝ)))
local instance sourceBoundFirstProper : ProperSpace (FirstFieldJet I) := by
  unfold FirstFieldJet
  infer_instance
local instance sourceBoundRestProper : ProperSpace (SecondFieldRestJet I) := by
  unfold SecondFieldRestJet
  infer_instance
local instance sourceBoundFullProper : ProperSpace (SecondFieldSourceJet I) := inferInstance

def firstFieldJetHolder
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix I I ℝ) α) (U1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) (T0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α)
    (T1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (F1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) : OAI.Analysis.Normed.Function.Holder.HolderMap X (FirstFieldJet I) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.pair (OAI.Analysis.Normed.Function.Holder.HolderMap.pair (OAI.Analysis.Normed.Function.Holder.HolderMap.pair A U1) (OAI.Analysis.Normed.Function.Holder.HolderMap.pair U2 T0)) (OAI.Analysis.Normed.Function.Holder.HolderMap.pair (OAI.Analysis.Normed.Function.Holder.HolderMap.pair T1 T2) F1)

omit [DecidableEq I] in
theorem norm_firstFieldJetHolder_le (hα : 0 ≤ α) {R : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix I I ℝ) α) (U1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) (T0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α)
    (T1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (F1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (hA : ‖A‖ ≤ R) (hU1 : ‖U1‖ ≤ R) (hU2 : ‖U2‖ ≤ R) (hT0 : ‖T0‖ ≤ R)
    (hT1 : ‖T1‖ ≤ R) (hT2 : ‖T2‖ ≤ R) (hF1 : ‖F1‖ ≤ R) :
    ‖firstFieldJetHolder A U1 U2 T0 T1 T2 F1‖ ≤ R :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα
    (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hA hU1) (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hU2 hT0))
    (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hT1 hT2) hF1)

def secondFieldJetHolder (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix I I ℝ) α) (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix I I ℝ) α)
    (U1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (U3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (T0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (T1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (T2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (T3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (S0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (S1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (S2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (F1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (F2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap X (SecondFieldSourceJet I) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.pair (OAI.Analysis.Normed.Function.Holder.HolderMap.pair (firstFieldJetHolder A U1 U2 T0 T1 T2 F1)
    (firstFieldJetHolder (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα DA S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα U2 S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα U3 S0)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T1 S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T2 S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T3 S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα F2 S0)))
    (OAI.Analysis.Normed.Function.Holder.HolderMap.pair (OAI.Analysis.Normed.Function.Holder.HolderMap.pair U3 DA) (OAI.Analysis.Normed.Function.Holder.HolderMap.pair S0 (OAI.Analysis.Normed.Function.Holder.HolderMap.pair S1 S2)))

omit [DecidableEq I] in
theorem norm_secondFieldJetHolder_le (hα : 0 ≤ α) {R : ℝ} (hR : 1 ≤ R)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix I I ℝ) α) (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix I I ℝ) α)
    (U1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (U3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (T0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (T1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (T2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (T3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (S0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (S1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (S2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (F1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (F2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (hA : ‖A‖ ≤ R) (hDA : ‖DA‖ ≤ R) (hU1 : ‖U1‖ ≤ R) (hU2 : ‖U2‖ ≤ R)
    (hU3 : ‖U3‖ ≤ R) (hT0 : ‖T0‖ ≤ R) (hT1 : ‖T1‖ ≤ R) (hT2 : ‖T2‖ ≤ R)
    (hT3 : ‖T3‖ ≤ R) (hS0 : ‖S0‖ ≤ R) (hS1 : ‖S1‖ ≤ R) (hS2 : ‖S2‖ ≤ R)
    (hF1 : ‖F1‖ ≤ R) (hF2 : ‖F2‖ ≤ R) :
    ‖secondFieldJetHolder hα A DA U1 U2 U3 T0 T1 T2 T3 S0 S1 S2 F1 F2‖ ≤ 2 * R ^ 2 := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRR : R ≤ 2 * R ^ 2 := by nlinarith
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα
  · apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα
    · exact (norm_firstFieldJetHolder_le hα A U1 U2 T0 T1 T2 F1
        hA hU1 hU2 hT0 hT1 hT2 hF1).trans hRR
    · have h1 := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le_of_norm_le hα hR0 DA S0 hDA hS0
      have h2 := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le_of_norm_le hα hR0 U2 S0 hU2 hS0
      have h3 := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le_of_norm_le hα hR0 U3 S0 hU3 hS0
      have h4 := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le_of_norm_le hα hR0 T1 S0 hT1 hS0
      have h5 := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le_of_norm_le hα hR0 T2 S0 hT2 hS0
      have h6 := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le_of_norm_le hα hR0 T3 S0 hT3 hS0
      have h7 := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le_of_norm_le hα hR0 F2 S0 hF2 hS0
      exact norm_firstFieldJetHolder_le hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα DA S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα U2 S0)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα U3 S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T1 S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T2 S0) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα T3 S0)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα F2 S0) h1 h2 h3 h4 h5 h6 h7
  · exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hU3 hDA)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hS0 (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hS1 hS2))).trans hRR

theorem exists_secondFieldExpression_holder_bound (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : OAI.Analysis.Normed.Function.Holder.HolderMap X (SecondFieldSourceJet I) α, ‖J‖ ≤ R →
      ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = secondFieldExpression (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x)) ∧ ‖F‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := @OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound X (SecondFieldSourceJet I) ℝ
    _ sourceBoundFullGroup sourceBoundFullSpace sourceBoundFullProper _ _ α
    (secondFieldExpression (I := I)) (contDiff_secondFieldExpression (I := I) 1) hα R hR
  refine ⟨C * (1 + R), by positivity, ?_⟩
  intro J hJ
  obtain ⟨F, hF, hFn⟩ := hbound J hJ
  exact ⟨F, hF, hFn.trans (mul_le_mul_of_nonneg_left (by linarith) hC)⟩

end OAI.Analysis.PDE.Dirichlet
