import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

/-! Fixed polynomial space for the actual complete conditioned query.
Retained words and local arithmetic work are counted independently of the
number of support pairs, attained signatures, head assignments or nodes. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets
open OAI SqrtLog SubexpLiftRing
open CostAssembly.Polynomial

/-- The actual node readout, ordered append, cleanup and next-index work. -/
def finishEnvelope (F X : ℕ) : ℕ :=
  29*F+27+(41*(2*F+3)+30000*(6*X+1)^6+1)+
    6*(F+X*(X*(2*X)))+9+4*F+10

/-- The actual reconstruction bound includes all arithmetic temporaries and
whole count-word readback. Its exponent is fixed before the query. -/
def recoveryEnvelope (F X : ℕ) : ℕ :=
  (2400*(ReconstructionProgram.Native.costConstant+1)^4+
    5*LeafProgram.Count.Prepare.ports.length+39628)*(F+X+1)^96

/-- A sum dominates the actual nested prefix maxima; it never multiplies
space by the number of executed candidates or callbacks. -/
def envelope (F P X : ℕ) : ℕ :=
  F+(67*F+37)+(919*F+31)+P+
    (896*F+(20000*(F+1)^4+300*(F+1))+finishEnvelope F X+1)+
    (896*F+recoveryEnvelope F X)

theorem actual_bounds (n t d J A S F P X : ℕ)
    (hn : n≤X) (ht : t≤X) (hd : d≤X) (hJ : J≤X) (hS : S≤X)
    (hF : QueryHeadBudgets.compact A≤F)
    (hP : StreamedQueryMeasuredCost.pairSpaceEnvelope A≤P) :
    QueryHeadBudgets.compact A≤envelope F P X ∧
    QueryStreamCorrect.nodeSpace n t d J A≤envelope F P X ∧
    QueryStreamCorrect.space n t d J A S≤envelope F P X := by
  have hfinish : QueryStreamCorrect.finishBudget n t d J A≤finishEnvelope F X := by
    apply (QueryNodeFinish.budget_polynomial n (baseWidth 3 t) d t J
      (QueryHeadBudgets.compact A)).trans
    unfold finishEnvelope
    simp only [RingProgram.ternary_baseWidth]
    gcongr
    omega
  have hprepare : QueryStreamCorrect.prepareBudget A≤20000*(F+1)^4+300*(F+1) := by
    unfold QueryStreamCorrect.prepareBudget
    gcongr
  have hrecovery : QueryReconstruction.budget (QueryHeadBudgets.compact A) S≤
      recoveryEnvelope F X := by
    apply (QueryReconstruction.budget_polynomial (QueryHeadBudgets.compact A) S).trans
    unfold recoveryEnvelope
    gcongr
  have hnode : QueryStreamCorrect.nodeSpace n t d J A≤envelope F P X := by
    unfold QueryStreamCorrect.nodeSpace envelope
    exact max_le (by omega) (by omega)
  refine ⟨?_,hnode,?_⟩
  · unfold envelope
    omega
  · unfold QueryStreamCorrect.space envelope at *
    exact max_le (by omega) (max_le (max_le (by omega) hnode) (by omega))

private theorem envelope_ordinary (f p : ℕ → ℕ)
    (hf : Ordinary f) (hp : Ordinary p) :
    Ordinary (fun X => envelope (f X) (p X) X) := by
  unfold envelope finishEnvelope recoveryEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add hf (ordinary_add (ordinary_mul (ordinary_const 67) hf) (ordinary_const 37))) (ordinary_add (ordinary_mul (ordinary_const 919) hf) (ordinary_const 31))) hp) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 896) hf) (ordinary_add (ordinary_mul (ordinary_const 20000) (ordinary_pow (ordinary_add hf (ordinary_const 1)) 4)) (ordinary_mul (ordinary_const 300) (ordinary_add hf (ordinary_const 1))))) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 29) hf) (ordinary_const 27)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 41) (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 3))) (ordinary_mul (ordinary_const 30000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 6) ordinary_id) (ordinary_const 1)) 6))) (ordinary_const 1))) (ordinary_mul (ordinary_const 6) (ordinary_add hf (ordinary_mul ordinary_id (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))))) (ordinary_const 9)) (ordinary_mul (ordinary_const 4) hf)) (ordinary_const 10))) (ordinary_const 1))) (ordinary_add (ordinary_mul (ordinary_const 896) hf) (ordinary_mul (ordinary_const (2400*(ReconstructionProgram.Native.costConstant+1)^4+5*LeafProgram.Count.Prepare.ports.length+39628)) (ordinary_pow (ordinary_add (ordinary_add hf ordinary_id) (ordinary_const 1)) 96))))

/-- Constants and degree are fixed before all input and source dimensions.
The bound contains only the actual scalar and word caps; neither assembled
runtime nor attained counts occur. -/
theorem complete_polynomial : ∃ C e : ℕ, ∀ n t d J A S : ℕ,
    QueryHeadBudgets.compact A≤C*(A+S+n+t+d+J+1)^e ∧
    QueryStreamCorrect.nodeSpace n t d J A≤C*(A+S+n+t+d+J+1)^e ∧
    QueryStreamCorrect.space n t d J A S≤C*(A+S+n+t+d+J+1)^e := by
  obtain ⟨CF,eF,hF⟩ := QueryHeadBudgets.caps_polynomial
  obtain ⟨CP,eP,hP⟩ := StreamedQueryMeasuredCost.pairSpaceEnvelope_polynomial
  let f : ℕ → ℕ := fun X => CF*(X+1)^eF
  let p : ℕ → ℕ := fun X => CP*(X+1)^eP
  have hf : Ordinary f := ordinary_mul (ordinary_const CF)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) eF)
  have hp : Ordinary p := ordinary_mul (ordinary_const CP)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) eP)
  obtain ⟨C,e,h⟩ := envelope_ordinary f p hf hp
  refine ⟨C,e,?_⟩
  intro n t d J A S
  let X := A+S+n+t+d+J
  have hAX : A+1≤X+1 := by dsimp [X]; omega
  have hFX : QueryHeadBudgets.compact A≤f X :=
    (hF A).1.trans (Nat.mul_le_mul_left CF (Nat.pow_le_pow_left hAX eF))
  have hPX : StreamedQueryMeasuredCost.pairSpaceEnvelope A≤p X :=
    (hP A).trans (Nat.mul_le_mul_left CP (Nat.pow_le_pow_left hAX eP))
  obtain ⟨hcompact,hnode,hspace⟩ := actual_bounds n t d J A S (f X) (p X) X
    (by dsimp [X]; omega) (by dsimp [X]; omega) (by dsimp [X]; omega)
    (by dsimp [X]; omega) (by dsimp [X]; omega) hFX hPX
  exact ⟨hcompact.trans (h X),hnode.trans (h X),hspace.trans (h X)⟩

/-- The fixed 896-tape source bank is counted in full, including retained
caller words; the compiler can consume this bound for every source prefix. -/
theorem all_stack_bits_polynomial : ∃ C e : ℕ, ∀ n t d J A S : ℕ,
    896*QueryStreamCorrect.space n t d J A S≤C*(A+S+n+t+d+J+1)^e := by
  obtain ⟨C,e,h⟩ := complete_polynomial
  refine ⟨896*C,e,?_⟩
  intro n t d J A S
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 896 (h n t d J A S).2.2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets
