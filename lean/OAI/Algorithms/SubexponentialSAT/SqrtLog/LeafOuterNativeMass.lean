import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeStage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeCollect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeScore

namespace OAI.Algorithms

/-! The fixed outer mass program: generate every marked reference, run each
native query, add all answers, construct the precision, normalize, and export.
The remaining semantic input is the actual query contract, discharged from
explicit native preparations by `marked_value_contract`. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def massBody (k : ℕ) : Cmd 40 896 :=
  .seq stageTrial (.seq references (.seq (collect k)
    (.seq makePrecision (.seq normalizeScore (exportWorker 322 769)))))
noncomputable def mass (k : ℕ) : Cmd 40 896 := protectCaller (massBody k)

def massPrecision (a : Data) : ℕ := LeafParametersProgram.precision
  (BinaryArithmetic.toNat (a.stacks 785)) (BinaryArithmetic.toNat (a.stacks 782))
def massRecords (a : Data) : List (List Bool) :=
  RowSelectionProgram.Index.alphabet (CounterPrograms.value (a.stacks 782))
def scoredState (a : Data) (z : ℕ) : Data :=
  ⟨fun _ => false,Function.update
    (Function.update (trialStaged a).stacks 212 (List.replicate (massPrecision a) true))
    322 (SubexpLiftRing.fixedBits (massPrecision a) z)⟩
noncomputable def massBodyBudget (a : Data) (queryCost width : List Bool → ℕ) (z : ℕ) : ℕ :=
  stageTrialCost a+routeCost (782,0) (trialStaged a)+References.budget (a.stacks 782)+1+
    Marked.Wide.valueBudget queryCost width (massRecords a) []+
    Precision.budget (a.stacks 785) (a.stacks 782)+1+
    (14*massPrecision a+2*Marked.Wide.outputGrowth width (massRecords a)+15)+
    exportCost 322 769 (scoredState a z)

def MassQueries (k : ℕ) (a : Data) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) : Prop :=
  ∀ b : Data, b.stacks=Function.update (trialStaged a).stacks 320
      (Encoding.encodeList id (massRecords a)) →
    Marked.Wide.QueryValueContract (Query.marked k) count queryCost width
      (fun w => w=Marked.Wide.workspace (projectState id workerStack b)) valid

private theorem trial_small_empty (a : Data) (ha : WorkerEmpty a) (i : Fin 896)
    (hi : i.val < 700) : (trialStaged a).stacks i=[] := by
  let j : Fin 768 := ⟨i.val,by omega⟩
  have hj : workerStack j=i := rfl
  rw [trialStaged_frame _ _ (by intro h; have hv := congrArg (fun x : Fin 896 => x.val) h; simp at hv; omega)
    (by intro h; have hv := congrArg (fun x : Fin 896 => x.val) h; simp at hv; omega) (by intro h; have hv := congrArg (fun x : Fin 896 => x.val) h; simp at hv; omega)
    (by intro h; have hv := congrArg (fun x : Fin 896 => x.val) h; simp at hv; omega) (by intro h; have hv := congrArg (fun x : Fin 896 => x.val) h; simp at hv; omega)
    (by intro h; have hv := congrArg (fun x : Fin 896 => x.val) h; simp at hv; omega)]
  exact hj ▸ ha j

private theorem trial_high_frame (a : Data) (i : Fin 896) (hi : 768 ≤ i.val) :
    (trialStaged a).stacks i=a.stacks i := by
  apply trialStaged_frame
  all_goals intro h; subst i; simp at hi

theorem massBody_eval (k : ℕ) (a : Data) (ha : WorkerEmpty a)
    (hm : BinaryArithmetic.toNat (a.stacks 782)≠0)
    (count queryCost width : List Bool → ℕ) (valid : List Bool → Prop)
    (hq : MassQueries k a count queryCost width valid)
    (hr : ∀ bits∈massRecords a, valid bits) (z : ℕ)
    (hz : (List.map count (massRecords a)).sum=z) (hcap : z < 2^massPrecision a) :
    ∃ t b, t ≤ massBodyBudget a queryCost width z ∧ Eval (massBody k) t a b ∧
      b.stacks=Function.update a.stacks 769 (SubexpLiftRing.fixedBits (massPrecision a) z) := by
  let s := trialStaged a
  have hstage := stageTrial_eval a (ha 767)
  have hs (i : Fin 896) (hi : i.val < 700) : s.stacks i=[] := trial_small_empty a ha i hi
  have hsh (i : Fin 896) (hi : 768 ≤ i.val) : s.stacks i=a.stacks i := trial_high_frame a i hi
  have hs767 : s.stacks 767=[] := by
    rw [trialStaged_frame _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha 767
  have hsready : ReferenceReady s := by
    refine ⟨hs767,?_⟩
    intro i hi
    apply hs
    rcases hi with hi|rfl <;> simp_all ; omega
  obtain ⟨tr,r,htr,her,hrs⟩ := references_eval s hsready
  have hrs' : r.stacks=Function.update s.stacks 320 (Encoding.encodeList id (massRecords a)) := by
    simpa [massRecords,ProgramEncoding.encodeRecords,hsh 782 (by decide)] using hrs
  have hr320 : r.stacks 320=Encoding.encodeList id (massRecords a) := by simp [hrs']
  have hrempty (i : Fin 896) (hi : i.val < 700) (hn : i≠320) : r.stacks i=[] := by
    simp [hrs',hn,hs i hi]
  obtain ⟨tc,c,htc,hec,hcv,hcl,hc320,hc321,hc323,hc324,hcf⟩ := collect_eval k
    count queryCost width valid r (massRecords a) (hq r hrs') hr hr320
    (hrempty 321 (by decide) (by decide)) (hrempty 323 (by decide) (by decide))
    (hrempty 324 (by decide) (by decide))
  have hcempt (i : Fin 896) (hi : i.val < 700) (hn : i≠322) : c.stacks i=[] := by
    by_cases h0 : i=320
    · subst i; exact hc320
    by_cases h1 : i=321
    · subst i; exact hc321
    by_cases h3 : i=323
    · subst i; exact hc323
    by_cases h4 : i=324
    · subst i; exact hc324
    rw [hcf i (by have := Fin.val_ne_of_ne h0; have := Fin.val_ne_of_ne h1
                  have := Fin.val_ne_of_ne hn; have := Fin.val_ne_of_ne h3
                  have := Fin.val_ne_of_ne h4; omega)]
    exact hrempty i hi h0
  have hch (i : Fin 896) (hi : 768 ≤ i.val) : c.stacks i=a.stacks i := by
    rw [hcf i (Or.inr (by omega)),hrs',Function.update_of_ne (by intro h; subst i; simp at hi)]
    exact hsh i hi
  have hcready : PrecisionReady c := by
    intro i hi
    apply hcempt
    · rcases hi with hi|rfl <;> simp_all ; omega
    · intro h; subst i; simp at hi
  have hcm : BinaryArithmetic.toNat (c.stacks 782)≠0 := by rw [hch 782 (by decide)]; exact hm
  obtain ⟨tp,p,htp,hep,hps⟩ := makePrecision_eval c hcready hcm
  have hps' : p.stacks=Function.update c.stacks 212 (List.replicate (massPrecision a) true) := by
    simpa [massPrecision,hch 782 (by decide),hch 785 (by decide)] using hps
  have hpready : ScoreReady p := by
    intro i hlo hhi
    have h212 : i≠212 := by intro h; subst i; simp at hlo
    rw [hps',Function.update_of_ne h212]
    exact hcempt i (by omega) (by intro h; subst i; simp at hlo)
  have hpwidth : p.stacks 212=List.replicate (massPrecision a) true := by simp [hps']
  have hpvalue : BinaryArithmetic.toNat (p.stacks 322)=z := by
    rw [hps',Function.update_of_ne (by decide : (322 : Fin 896)≠212),hcv,hz,
      hrempty 322 (by decide) (by decide)]
    simp [BinaryArithmetic.toNat]
  obtain ⟨tn,f,htn,hen,hfs⟩ := normalizeScore_eval p hpready z
    (by simpa [hpwidth] using hcap) hpvalue
  have hfs' : f.stacks=Function.update p.stacks 322 (SubexpLiftRing.fixedBits (massPrecision a) z) := by
    simpa [hpwidth] using hfs
  have hfcanon : f.stacks=(scoredState a z).stacks := by
    funext i
    by_cases h322 : i=322
    · subst i; simp [hfs',scoredState]
    by_cases h212 : i=212
    · subst i; simp [hfs',hps',scoredState]
    simp only [hfs',hps',scoredState,Function.update_of_ne h322,Function.update_of_ne h212]
    by_cases h320 : i=320
    · subst i; exact hc320.trans (hs 320 (by decide)).symm
    by_cases h321 : i=321
    · subst i; exact hc321.trans (hs 321 (by decide)).symm
    by_cases h323 : i=323
    · subst i; exact hc323.trans (hs 323 (by decide)).symm
    by_cases h324 : i=324
    · subst i; exact hc324.trans (hs 324 (by decide)).symm
    rw [hcf i (by have := Fin.val_ne_of_ne h320; have := Fin.val_ne_of_ne h321
                  have := Fin.val_ne_of_ne h322; have := Fin.val_ne_of_ne h323
                  have := Fin.val_ne_of_ne h324; omega),hrs',Function.update_of_ne h320]
  have hf767 : f.stacks 767=[] := by simpa [hfcanon,scoredState] using hs767
  have hex := exportWorker_eval 322 (by decide) 769 (by decide) f hf767
  have hexCost : exportCost 322 769 f=exportCost 322 769 (scoredState a z) := by
    simp [exportCost,routeCost,routed,Cleanup.Wide.budget,Cleanup.Wide.bytes,projectState,hfcanon]
  refine ⟨stageTrialCost a+(tr+(tc+(tp+(tn+exportCost 322 769 f)))),
    exportedWorker 322 769 f,?_,hstage.seq (her.seq (hec.seq (hep.seq (hen.seq hex)))),?_⟩
  · have hr322 := hrempty 322 (by decide) (by decide)
    simp only [hr322] at htc hcl
    simp only [List.length_nil,zero_add] at hcl
    rw [hsh 782 (by decide)] at htr
    rw [hch 785 (by decide),hch 782 (by decide)] at htp
    have hp322 : p.stacks 322=c.stacks 322 := by simp [hps']
    rw [hpwidth,hp322,List.length_replicate] at htn
    rw [hexCost]
    unfold massBodyBudget
    dsimp only [s] at htr
    omega
  · funext i
    by_cases h769 : i=769
    · subst i
      rw [exportedWorker_output _ _ _ (by decide)]
      simp [hfcanon,scoredState,workerStack]
    by_cases hlo : i.val < 768
    · let j : Fin 768 := ⟨i.val,hlo⟩
      have hj : workerStack j=i := rfl
      rw [Function.update_of_ne h769,←hj,exportedWorker_empty]
      exact (ha j).symm
    · rw [Function.update_of_ne h769,exportedWorker_frame _ _ _ _ (by omega) h769,hfcanon]
      have h212 : i≠212 := by intro h; subst i; simp at hlo
      have h322 : i≠322 := by intro h; subst i; simp at hlo
      simp only [scoredState,Function.update_of_ne h212,Function.update_of_ne h322]
      exact hsh i (by omega)

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
