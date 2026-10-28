import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFrame

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def metadataIndices : Finset (Fin 200) := {64,65,66,67,68,69}
def metadataFieldsLength (a : Data) : ℕ :=
  ∑ i ∈ metadataIndices,(a.stacks (i.castAdd 56)).length
def MetadataReady (a : Data) : Prop :=
  ∀ j : Fin 256, j.val < 200 → (j.val < 64 ∨ 70 ≤ j.val) → a.stacks j=[]

theorem metadataFieldsLength_eq (a : Data) : metadataFieldsLength a=
    (a.stacks 64).length+(a.stacks 65).length+(a.stacks 66).length+
    (a.stacks 67).length+(a.stacks 68).length+(a.stacks 69).length := by
  simp [metadataFieldsLength,metadataIndices]
  omega

theorem work_sum_metadata (a : Data) (h : MetadataReady a) :
    (workPorts.map (fun j => (a.stacks j).length)).sum=metadataFieldsLength a := by
  simp only [workPorts,List.map_ofFn,List.sum_ofFn,Function.comp_def,metadataFieldsLength]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hi' : (i.val < 64) ∨ (70 ≤ i.val) := by
    by_contra hn
    have hx : i.val=64 ∨ i.val=65 ∨ i.val=66 ∨ i.val=67 ∨ i.val=68 ∨ i.val=69 := by omega
    rcases hx with hx|hx|hx|hx|hx|hx
    all_goals
      apply hi
      simp only [metadataIndices,Finset.mem_insert,Finset.mem_singleton]
      first | exact Or.inl (Fin.ext hx)
            | exact Or.inr (Or.inl (Fin.ext hx))
            | exact Or.inr (Or.inr (Or.inl (Fin.ext hx)))
            | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hx))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hx)))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext hx)))))
  simpa using congrArg List.length (h (i.castAdd 56) i.isLt hi')

theorem cleanup_metadata_cost (a : Data) (h : MetadataReady a) :
    Staging.cost 0 1 cleanupOps a ≤ 2*metadataFieldsLength a+600 := by
  simpa only [work_sum_metadata a h] using cleanup_cost a

/-- The uncovered row branch is an actual comparison, conditional push, and
cleanup. It needs no coverage semantics: those are supplied by the caller. -/
theorem uncovered_cleanup_eval (a : Data) (h : MetadataReady a)
    (h254 : a.stacks 254=[]) :
    ∃ n ≤ 27*((a.stacks 252).length+(a.stacks 253).length)+
        2*metadataFieldsLength a+635,
      ∃ z : Data, Eval (.seq uncovered cleanup) n a z ∧
      (∀ j : Fin 256, z.stacks j=
        if j.val < 200 then [] else if j=254 then
          (if a.stacks 252=a.stacks 253 then [true] else []) else a.stacks j) := by
  obtain ⟨nc,hnc,b,he,hbs,_,h7⟩ := compareIndices_eval a
    (fun j hj => h j (by omega) (Or.inl (by omega)))
  have hbt : b.stacks 199=[] := by rw [hbs]; exact h 199 (by decide) (Or.inr (by decide))
  have hbready : MetadataReady b := by intro j hj hk; rw [hbs]; exact h j hj hk
  have hbmass : metadataFieldsLength b=metadataFieldsLength a := by
    simp only [metadataFieldsLength,hbs]
  by_cases heq : a.stacks 252=a.stacks 253
  · let c := TupleProgram.pushedState (254 : Fin 256) (0 : Fin 16) true b
    have hp := TupleProgram.pushConst_eval (254 : Fin 256) (0 : Fin 16) true b
    have hcst : c.stacks=Function.update a.stacks 254 [true] := by
      simp [c,hbs,h254]
    have hct : c.stacks 199=[] := by simp [hcst]; exact h 199 (by decide) (Or.inr (by decide))
    have hcready : MetadataReady c := by
      intro j hj hk
      have hn : j≠254 := by intro hz; subst j; norm_num at hj
      simpa [hcst,hn] using h j hj hk
    have hcmass : metadataFieldsLength c=metadataFieldsLength a := by
      simp [metadataFieldsLength_eq,hcst]
    have hc := cleanup_metadata_cost c hcready
    have hbranch := Eval.ite_true (no := (.base .skip : Code))
      (show b.regs 7=true by simp [h7,heq]) hp
    refine ⟨nc+3+Staging.cost 0 1 cleanupOps c,?_,Staging.result 0 1 cleanupOps c,
      (he.seq hbranch).seq (cleanup_eval c hct),?_⟩
    · rw [hcmass] at hc
      omega
    · intro j
      rw [cleanup_stacks,hcst]
      simp [heq,Function.update_apply]
  · have hc := cleanup_metadata_cost b hbready
    have hbranch := Eval.ite_false (yes := (TupleProgram.pushConst 254 0 true : Code))
      (show b.regs 7=false by simp [h7,heq]) (Eval.base (StructuredProgram.Eval.skip b))
    refine ⟨nc+1+Staging.cost 0 1 cleanupOps b,?_,Staging.result 0 1 cleanupOps b,
      (he.seq hbranch).seq (cleanup_eval b hbt),?_⟩
    · rw [hbmass] at hc
      omega
    · intro j
      rw [cleanup_stacks,hbs]
      by_cases hj : j=254
      · subst j; simp [heq,h254]
      · simp [hj]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
