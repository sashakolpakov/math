import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchContextBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryMaskedNative

namespace OAI.Algorithms

/-! Physical marked/unmarked staging supplies the input frames and four
blank loop cells required by the branch-context constructor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchContext
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem marked_protected (a : Factor.Data) (i : Fin 768)
    (hp : Query.Protected i) (_ : i≠323) : (Query.markedInput a).stacks i=a.stacks i := by
  apply Query.markedInput_frame
  all_goals
    intro he
    subst i
    simp [Query.Protected] at hp

 theorem unmarked_protected (a : Factor.Data) (i : Fin 768)
    (hp : Query.Protected i) (_ : i≠323) : (Query.unmarkedInput a).stacks i=a.stacks i := by
  apply Query.unmarkedInput_frame
  all_goals
    intro he
    subst i
    simp [Query.Protected] at hp

 theorem marked_masked_blanks (a : Factor.Data) (hc : Query.CleanWork a) :
    ∀i,i∈blankPorts → (Query.markedInput (Query.Carried.reference a)).stacks i=[] := by
  intro i hi
  have hz := cleanWork_blanks (initial:=a) hc i hi
  simp only [blankPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals
    exact (Query.markedInput_frame _ _ (by decide) (by decide) (by decide)).trans
      ((Query.Carried.reference_visible a _ (by decide)).trans hz)

 theorem unmarked_masked_blanks (a : Factor.Data) (hc : Query.CleanWork a) :
    ∀i,i∈blankPorts → (Query.unmarkedInput (Query.Carried.reference a)).stacks i=[] := by
  intro i hi
  have hz := cleanWork_blanks (initial:=a) hc i hi
  simp only [blankPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals
    exact (Query.unmarkedInput_frame _ _ (by decide) (by decide)).trans
      ((Query.Carried.reference_visible a _ (by decide)).trans hz)

 theorem marked_base_protected {q : LeafQueryFrontend.Query} {k : ℕ} (a : Factor.Data)
    {hg : Guard (q.input k)} {W V L : ℕ}
    (p : Query.Preparation q k (Query.markedInput (Query.Carried.reference a)) hg W V L)
    (i : Fin 768) (hp : Query.Protected i) (hne : i≠323) :
    (base p).stacks i=(Query.Carried.reference a).stacks i :=
  base_protected p _ (marked_protected _) i hp hne

 theorem unmarked_base_protected {q : LeafQueryFrontend.Query} {k : ℕ} (a : Factor.Data)
    {hg : Guard (q.input k)} {W V L : ℕ}
    (p : Query.Preparation q k (Query.unmarkedInput (Query.Carried.reference a)) hg W V L)
    (i : Fin 768) (hp : Query.Protected i) (hne : i≠323) :
    (base p).stacks i=(Query.Carried.reference a).stacks i :=
  base_protected p _ (unmarked_protected _) i hp hne

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchContext

end OAI.Algorithms
