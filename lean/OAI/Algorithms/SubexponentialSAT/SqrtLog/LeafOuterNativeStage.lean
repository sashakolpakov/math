import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryTypedSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStage
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Measured source staging for both native outer queries. The saved decoder
width is copied literally; the trial prefix is written by a native escape
loop rather than supplied as an already encoded query. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram
open Subexp

abbrev Data := State 40 896

def masterRoutes : List Route := [(784,700),(782,707),(783,708),(785,709),(777,701)]
abbrev stageFinal : Cmd 40 896 := routes masterRoutes
def finalStaged (a : Data) : Data := routesState masterRoutes a
def stageFinalCost (a : Data) : ℕ := routesCost masterRoutes a

theorem masterRoutes_valid : ∀ p ∈ masterRoutes, routeValid p := by
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl <;> unfold routeValid <;> decide

theorem stageFinal_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval stageFinal (stageFinalCost a) a (finalStaged a) :=
  routes_eval masterRoutes masterRoutes_valid a ht

theorem finalStaged_sources (a : Data) :
    (finalStaged a).stacks 700=a.stacks 784 ∧
    (finalStaged a).stacks 701=a.stacks 777 ∧
    (finalStaged a).stacks 707=a.stacks 782 ∧
    (finalStaged a).stacks 708=a.stacks 783 ∧
    (finalStaged a).stacks 709=a.stacks 785 := by
  simp [finalStaged,masterRoutes,routesState,routed]

theorem finalStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (finalStaged a).stacks i=a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact Ne.symm h0
  · exact Ne.symm h7
  · exact Ne.symm h8
  · exact Ne.symm h9
  · exact Ne.symm h1

def trialPorts : RecordPrograms.Ports 40 896 :=
  ⟨0,1,2,702,701,by decide,by decide,by decide,by decide⟩

abbrev prefixTrial : Cmd 40 896 :=
  .seq (route (768,702))
    (.seq (TupleProgram.pushConst 701 0 false)
      (.seq (TupleProgram.escape trialPorts) (TupleProgram.pushConst 701 0 true)))

def prefixed (a : Data) : Data :=
  TupleProgram.pushedState 701 0 true
    (TupleProgram.escapedState trialPorts
      (TupleProgram.pushedState 701 0 false (routed (768,702) a)))

def prefixCost (a : Data) : ℕ := routeCost (768,702) a+5*(a.stacks 768).length+7

theorem prefixTrial_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval prefixTrial (prefixCost a) a (prefixed a) := by
  have h1 := route_eval (768,702) (by unfold routeValid; decide) a ht
  have h2 := TupleProgram.pushConst_eval (701:Fin 896) (0:Fin 40) false (routed (768,702) a)
  have h3 := TupleProgram.escape_eval_state trialPorts
    (TupleProgram.pushedState 701 0 false (routed (768,702) a))
  have h4 := TupleProgram.pushConst_eval (701:Fin 896) (0:Fin 40) true
    (TupleProgram.escapedState trialPorts
      (TupleProgram.pushedState 701 0 false (routed (768,702) a)))
  convert h1.seq (h2.seq (h3.seq h4)) using 1 <;>
    simp [prefixCost,prefixed,trialPorts,TupleProgram.pushedState,routed] ; omega

theorem prefixed_rows (a : Data) :
    (prefixed a).stacks 701=true::(Encoding.frame (a.stacks 768).reverse++a.stacks 701) := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,
    TupleProgram.frame_eq_escaped,List.append_assoc]

theorem prefixed_scratch (a : Data) : (prefixed a).stacks 702=[] := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed]

theorem prefixed_frame (a : Data) (i : Fin 896) (h1 : i≠701) (h2 : i≠702) :
    (prefixed a).stacks i=a.stacks i := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,h1,h2]

abbrev stageTrial : Cmd 40 896 := .seq stageFinal prefixTrial
def trialStaged (a : Data) : Data := prefixed (finalStaged a)
def stageTrialCost (a : Data) : ℕ := stageFinalCost a+prefixCost (finalStaged a)

theorem stageTrial_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval stageTrial (stageTrialCost a) a (trialStaged a) := by
  exact (stageFinal_eval a ht).seq (prefixTrial_eval (finalStaged a)
    ((finalStaged_frame a 767 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht))

theorem trialStaged_sources (a : Data) :
    (trialStaged a).stacks 700=a.stacks 784 ∧
    (trialStaged a).stacks 701=true::(Encoding.frame (a.stacks 768).reverse++a.stacks 777) ∧
    (trialStaged a).stacks 707=a.stacks 782 ∧
    (trialStaged a).stacks 708=a.stacks 783 ∧
    (trialStaged a).stacks 709=a.stacks 785 := by
  have h := finalStaged_sources a
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (prefixed_frame _ 700 (by decide) (by decide)).trans h.1
  · rw [trialStaged,prefixed_rows,h.2.1,
      finalStaged_frame a 768 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact (prefixed_frame _ 707 (by decide) (by decide)).trans h.2.2.1
  · exact (prefixed_frame _ 708 (by decide) (by decide)).trans h.2.2.2.1
  · exact (prefixed_frame _ 709 (by decide) (by decide)).trans h.2.2.2.2

theorem trialStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h2 : i≠702) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (trialStaged a).stacks i=a.stacks i :=
  (prefixed_frame _ i h1 h2).trans (finalStaged_frame a i h0 h1 h7 h8 h9)

theorem final_sources {q : LeafQueryFrontend.Query} {a : Data}
    (h : OuterQuery.FinalWords q a) :
    LeafProgram.Query.Sources q (projectState id workerStack (finalStaged a)) := by
  obtain ⟨hf,hr,hm,hw,hn⟩ := finalStaged_sources a
  exact h.staged _ hf hr hm hw hn

theorem trial_sources {q : LeafQueryFrontend.Query} {a : Data}
    (h : OuterQuery.TrialWords q a) :
    LeafProgram.Query.Sources q (projectState id workerStack (trialStaged a)) := by
  obtain ⟨hf,hr,hm,hw,hn⟩ := trialStaged_sources a
  exact h.staged _ hf hr hm hw hn

theorem final_clean (a : Data) (ha : WorkerEmpty a) :
    LeafProgram.Query.CleanWork (projectState id workerStack (finalStaged a)) := by
  intro i hi _
  have hn (j : Fin 768) (hj : LeafProgram.Query.Protected j) : i≠j := by
    intro he; subst i; exact hi hj
  change (finalStaged a).stacks (workerStack i)=[]
  have h0 : workerStack i≠700 := fun h => hn 700 (by decide) (Fin.castAdd_injective 768 128 h)
  have h1 : workerStack i≠701 := fun h => hn 701 (by decide) (Fin.castAdd_injective 768 128 h)
  have h7 : workerStack i≠707 := fun h => hn 707 (by decide) (Fin.castAdd_injective 768 128 h)
  have h8 : workerStack i≠708 := fun h => hn 708 (by decide) (Fin.castAdd_injective 768 128 h)
  have h9 : workerStack i≠709 := fun h => hn 709 (by decide) (Fin.castAdd_injective 768 128 h)
  rw [finalStaged_frame a _ h0 h1 h7 h8 h9]
  exact ha i

theorem trial_clean (a : Data) (ha : WorkerEmpty a) :
    LeafProgram.Query.CleanWork (projectState id workerStack (trialStaged a)) := by
  intro i hi h321
  by_cases h702 : i=702
  · subst i; exact prefixed_scratch (finalStaged a)
  have h1 : workerStack i≠701 := by
    intro he; apply hi; have he' : i=701 := Fin.castAdd_injective 768 128 he
    subst i; decide
  have h2 : workerStack i≠702 := by
    intro he; exact h702 (Fin.castAdd_injective 768 128 he)
  change (prefixed (finalStaged a)).stacks (workerStack i)=[]
  rw [prefixed_frame _ _ h1 h2]
  exact final_clean a ha i hi h321

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
