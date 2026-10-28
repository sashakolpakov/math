import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

abbrev Data := State 40 896

def masterRoutes : List Route := [(784,700),(782,707),(783,708),(785,709),(777,701)]
def stageFinal : Cmd 40 896 := routes masterRoutes
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

def prefixTrial : Cmd 40 896 :=
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
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  all_goals simp [prefixTrial, prefixCost, prefixed, trialPorts,
    SqrtLog.LeafOuterProgram.routed, TupleProgram.pushedState]
  omega

theorem prefixed_rows (a : Data) :
    (prefixed a).stacks 701=true::(Encoding.frame (a.stacks 768).reverse++a.stacks 701) := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,
    TupleProgram.frame_eq_escaped,List.append_assoc]

theorem prefixed_scratch (a : Data) : (prefixed a).stacks 702=[] := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed]

theorem prefixed_frame (a : Data) (i : Fin 896) (h1 : i≠701) (h2 : i≠702) :
    (prefixed a).stacks i=a.stacks i := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,h1,h2]

def stageTrial : Cmd 40 896 := .seq stageFinal prefixTrial
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
