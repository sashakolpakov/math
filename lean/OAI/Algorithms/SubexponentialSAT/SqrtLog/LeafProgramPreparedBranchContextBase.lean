import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchWidth

namespace OAI.Algorithms

/-! The branch loop's initial cells and protected frame are obtained from the
actual query preparation. Only its four pre-existing loop cells need to be
blank; the reader cells are cleared by the executed Count.Prepare program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchContext
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

 def base : Factor.Data := Marked.Wide.maskCopied (Query.prepared p.out)
 def blankPorts : List (Fin 768) := [330,331,332,333]

 theorem output_loop_frame (i : Fin 768) (hi : i∈([321,330,331,332,333] : List (Fin 768))) :
    p.out.stacks i=initial.stacks i := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals
    exact (p.arithmeticOutput.collectorFrame _ (by decide) (by decide)).trans
      ((p.packingFrame _ (by decide) (by decide) (by decide)).trans
        (p.frontOutput.frame _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)))

 theorem prepared_loop_frame (i : Fin 768) (hi : i∈([321,330,331,332,333] : List (Fin 768))) :
    (Query.prepared p.out).stacks i=initial.stacks i := by
  apply Eq.trans _ (output_loop_frame p i hi)
  by_cases h321 : i=321
  · subst i
    exact Query.prepared_reader_frame p.out 321 (by decide) (by decide)
  have hlo : 330 ≤ i.val := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with hi|rfl|rfl|rfl|rfl
    · exact (h321 hi).elim
    all_goals decide
  have h699 : i≠699 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  exact (Count.Prepare.output_high_frame _ i hlo h699).trans
    (Samples.prepared_frame p.out i (by intro h; subst i; norm_num at hlo)
      (by intro h; subst i; norm_num at hlo))

 theorem base_loop_frame (i : Fin 768) (hi : i∈([321,330,331,332] : List (Fin 768))) :
    (base p).stacks i=initial.stacks i := by
  have hn : i≠333 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> decide
  exact (Marked.Wide.maskCopied_frame _ i hn).trans
    (prepared_loop_frame p i (by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi ⊢; tauto))

 theorem base_mask (h333 : initial.stacks 333=[]) : (base p).stacks 333=q.forward.reverse := by
  have he := (prepared_loop_frame p 333 (by simp)).trans h333
  exact (Marked.Wide.maskCopied_mask _ he).trans
    ((Marked.Wide.maskCopied_frame (Query.prepared p.out) 338 (by decide)).symm.trans
      (PreparedSource.query_mask p))

 theorem base_empty (hb : ∀i,i∈blankPorts → initial.stacks i=[]) :
    (base p).stacks 330=[] ∧ (base p).stacks 331=[] ∧ (base p).stacks 332=[] ∧
      (base p).stacks 323=[] ∧ (base p).stacks 324=[] := by
  refine ⟨(base_loop_frame p 330 (by simp)).trans (hb 330 (by simp [blankPorts])),
    (base_loop_frame p 331 (by simp)).trans (hb 331 (by simp [blankPorts])),
    (base_loop_frame p 332 (by simp)).trans (hb 332 (by simp [blankPorts])),?_,?_⟩
  · exact (Marked.Wide.maskCopied_frame _ 323 (by decide)).trans
      (Count.Prepare.output_reader _ 323 (by simp))
  · exact (Marked.Wide.maskCopied_frame _ 324 (by decide)).trans
      (Count.Prepare.output_reader _ 324 (by simp))

 theorem base_reference_length (hw : ∀i,(initial.stacks i).length ≤ W) :
    ((base p).stacks 321).length ≤ Query.Width.incomingWidth p := by
  exact (congrArg List.length (Marked.Wide.maskCopied_frame _ 321 (by decide))).le.trans
    (PreparedSource.prepared_width_incoming p hw 321)

 theorem base_protected_initial (i : Fin 768) (hp : Query.Protected i) (hne : i≠323) :
    (base p).stacks i=initial.stacks i := by
  have hb : i=320 ∨ i=322 ∨ 700 ≤ i.val := by
    rcases hp with h|h|h|h|h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact (hne h).elim
    all_goals right; right
    all_goals first | (subst i; decide) | omega
  have hclear : i∉Count.Prepare.ports := by
    rcases hb with rfl|rfl|hi
    · exact Count.Prepare.ports_gap 320 (by norm_num) (by norm_num)
    · exact Count.Prepare.ports_gap 322 (by norm_num) (by norm_num)
    · intro he
      have hh := Count.Prepare.ports_lt i he
      omega
  have h333 : i≠333 := by
    rcases hb with rfl|rfl|hi
    · decide
    · decide
    · intro he; subst i; norm_num at hi
  have h699 : i≠699 := by
    rcases hb with rfl|rfl|hi
    · decide
    · decide
    · intro he; subst i; norm_num at hi
  have h190 : i≠190 := by
    rcases hb with rfl|rfl|hi
    · decide
    · decide
    · intro he; subst i; norm_num at hi
  have h191 : i≠191 := by
    rcases hb with rfl|rfl|hi
    · decide
    · decide
    · intro he; subst i; norm_num at hi
  exact (Marked.Wide.maskCopied_frame _ i h333).trans
    ((Count.Prepare.output_frame _ i hclear h699).trans
      ((Samples.prepared_frame p.out i h190 h191).trans (p.protected_frame i hp)))

 theorem base_protected (original : Factor.Data)
    (hf : ∀i,Query.Protected i → i≠323 → initial.stacks i=original.stacks i)
    (i : Fin 768) (hp : Query.Protected i) (hne : i≠323) :
    (base p).stacks i=original.stacks i := (base_protected_initial p i hp hne).trans (hf i hp hne)

 theorem cleanWork_blanks (hc : Query.CleanWork initial) :
    ∀i,i∈blankPorts → initial.stacks i=[] := by
  intro i hi
  simp only [blankPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals exact hc _ (by decide) (by decide)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchContext

end OAI.Algorithms
