import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryConstruct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramSerializationBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesFinal

namespace OAI.Algorithms

/-! Actual query input and canonical model size bounds. Original input-word
padding remains explicit; no current state width is renamed as input width. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
open ProducedQueryResources CostAssembly.Polynomial
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem capacity_le (q : LeafQueryFrontend.Query) (k W : ℕ) (a : Data)
    (hr : q.Ready a) (hw : ∀i,(a.stacks i).length ≤ W) :
    LeafScopeInputBounds.capacity q k ≤ 6*W+ambient q+k+8 := by
  have h0 := hw 700
  have h1 := hw 701
  have h2 := hw 705
  have h3 := hw 707
  have h4 := hw 708
  have h5 := hw 709
  rw [hr.1] at h0
  rw [hr.2.1] at h1
  rw [hr.2.2.1] at h2
  rw [hr.2.2.2.2.1] at h3
  rw [hr.2.2.2.2.2.1] at h4
  rw [hr.2.2.2.2.2.2.1] at h5
  unfold LeafScopeInputBounds.capacity ambient
  omega

 theorem model_values_le (x : Input) (l : Fin 8 → ℕ) (V : ℕ)
    (h : ∀i,(Circuit.result Serialization.code (Execute.guardedModel x l)).val i ≤ V) :
    ∀i,(Execute.guardedModel x l).val i ≤ V := by
  intro i
  by_cases h44 : i=44
  · subst i; simp [Execute.guardedModel]
  by_cases h45 : i=45
  · subst i; simp [Execute.guardedModel]
  exact (Serialization.frame _ i h44 h45) ▸ h i

 theorem model_lengths_polynomial : ∃ C d : ℕ, ∀ q : LeafQueryFrontend.Query,
    ∀ k, q.Valid → ∀l, l=q.inputLengths k →
    modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)) ≤
      C*(LeafScopeInputBounds.capacity q k+1)^d := by
  obtain ⟨C,d,h⟩ := Serialization.uniform_guarded_lengths_polynomial
  have hp : Ordinary (fun S => C*(LeafQueryFrontend.parameterSize S+1)^d) := by
    unfold LeafQueryFrontend.parameterSize
    repeat first | apply ordinary_add | apply ordinary_mul | apply ordinary_pow
                 | exact ordinary_id | apply ordinary_const
  obtain ⟨A,e,he⟩ := hp
  refine ⟨A,e,?_⟩
  intro q k hv l hl
  subst l
  apply le_trans _ (he _)
  apply modelLengthCap_le
  exact h (q.input k) (q.inputLengths k) _
    (LeafQueryFrontend.parameter_counts_bound q k hv)
    (LeafQueryFrontend.parameter_lengths_bound q k hv)

 theorem model_before_lengths_le (x : Input) (l : Fin 8 → ℕ) (L : ℕ)
    (h : modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel x l)) ≤ L) :
    ∀i,(Execute.guardedModel x l).len i ≤ L := by
  intro i
  have hi : (Circuit.result Serialization.code (Execute.guardedModel x l)).len i ≤ L :=
    (Finset.le_sup (Finset.mem_univ i)).trans h
  by_cases h44 : i=44
  · subst i; simp [Execute.guardedModel]
  by_cases h45 : i=45
  · subst i; simp [Execute.guardedModel]
  simpa only [Serialization.lengths,ite_eq_right h44,ite_eq_right h45] using hi

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
