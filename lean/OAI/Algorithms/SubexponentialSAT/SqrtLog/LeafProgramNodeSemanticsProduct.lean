import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsShift

namespace OAI.Algorithms

/-! Head-local canonical products are reassembled into the exact common
source path. No local or global factor truth table is introduced. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open IdempotentApplyProgram.Steps (Context)
open AssignmentSemantics
noncomputable section

variable {R : Type*} [CommRing R]

theorem canonical_finite_prod {V G : Type*} [DecidableEq V] [Fintype G]
    (u J : ℕ) (f : G → Squarefree.Jet V R) :
    Squarefree.canonical u J (∏ g, Squarefree.canonical u J (f g)) =
      Squarefree.canonical u J (∏ g, f g) := by
  classical
  have h (s : Finset G) :
      Squarefree.canonical u J (∏ g ∈ s, Squarefree.canonical u J (f g)) =
        Squarefree.canonical u J (∏ g ∈ s, f g) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert g s hg ih =>
      rw [Finset.prod_insert hg,Finset.prod_insert hg,Moments.canonical_mul_left]
      rw [← Moments.canonical_mul_right u J (f g),ih,Moments.canonical_mul_right]
  exact h Finset.univ

/-- The output of each real selectedRun can supply hD using
AssignmentSemantics.selectedRun_polynomial. -/
theorem colored_products_query {p t n d : ℕ} [Fact p.Prime]
    (ctx : Context p t n d) (hu : ctx.u=t)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    {G : Type*} [Fintype G] [DecidableEq G]
    (ids : List ℕ) (hn : ids.Nodup) (color : ℕ → G)
    (jet : G → ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (D : G → Squarefree.Jet (Fin n) R)
    (path : ℕ → Fin n → R[X]) (theta : R)
    (x : Fin n → R) (hx : ∀ v, x v*x v=x v)
    (hjet : ∀ g id v, Moments.jetEval x hx (jet g id v)=
      Polynomial.C (shift theta (path id v)))
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (hh : ∀ i < hashes.length, i∈ids) (hm : marked=true → hashes.length∈ids)
    (hD : ∀ g, D g=Squarefree.canonical ctx.u ctx.J
      (((ids.filter (fun i => color i=g)).map
        (selectedValue ctx scalar basis code (jet g) hashes marked clause)).prod)) :
    Truncation.trunc ctx.J (Moments.sumUCoeff ctx.u (Moments.jetEval x hx (∏ g,D g))) =
      Truncation.trunc ctx.J ((queryPolynomial t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path).comp (Polynomial.X+Polynomial.C theta)) := by
  rw [← Moments.evaluated_readout_canonical ctx.u ctx.J (∏ g,D g) x hx]
  simp_rw [hD]
  rw [canonical_finite_prod,Moments.evaluated_readout_canonical,map_prod]
  simp only [map_list_prod,List.map_map,Function.comp_def]
  simp_rw [selectedValue_eval ctx scalar basis code _ _ x hx (hjet _)]
  rw [prod_colored_lists ids hn color,hu]
  exact selectedExpressions_readout t ctx.J (codeDigits ctx scalar code) _ marked clause path theta
    ids hn (by simpa using hh) (by simpa using hm)

/-- The output of each real selectedRun can supply hD using
AssignmentSemantics.selectedRun_polynomial. -/
theorem colored_products_query_selected {p t n d : ℕ} [Fact p.Prime]
    (ctx : Context p t n d) (hu : ctx.u=t)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    {G : Type*} [Fintype G] [DecidableEq G]
    (ids : List ℕ) (hn : ids.Nodup) (color : ℕ → G)
    (jet : G → ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (D : G → Squarefree.Jet (Fin n) R)
    (path : ℕ → Fin n → R[X]) (theta : R)
    (x : Fin n → R) (hx : ∀ v, x v*x v=x v)
    (hjet : ∀ g id, id∈ids → color id=g → ∀ v, Moments.jetEval x hx (jet g id v)=
      Polynomial.C (shift theta (path id v)))
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (hh : ∀ i < hashes.length, i∈ids) (hm : marked=true → hashes.length∈ids)
    (hD : ∀ g, D g=Squarefree.canonical ctx.u ctx.J
      (((ids.filter (fun i => color i=g)).map
        (selectedValue ctx scalar basis code (jet g) hashes marked clause)).prod)) :
    Truncation.trunc ctx.J (Moments.sumUCoeff ctx.u (Moments.jetEval x hx (∏ g,D g))) =
      Truncation.trunc ctx.J ((queryPolynomial t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path).comp (Polynomial.X+Polynomial.C theta)) := by
  rw [← Moments.evaluated_readout_canonical ctx.u ctx.J (∏ g,D g) x hx]
  simp_rw [hD]
  rw [canonical_finite_prod,Moments.evaluated_readout_canonical,map_prod]
  simp only [map_list_prod,List.map_map,Function.comp_def]
  have he (g : G) :
      ((ids.filter (fun i => color i=g)).map (fun id =>
        Moments.jetEval x hx (selectedValue ctx scalar basis code (jet g) hashes marked clause id))).prod =
      ((ids.filter (fun i => color i=g)).map (selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause (fun id v => shift theta (path id v)))).prod := by
    congr 1
    apply List.map_congr_left
    intro id hi
    have hm := List.mem_filter.mp hi
    exact selectedValue_eval_at ctx scalar basis code (jet g) _ x hx hashes marked clause id
      (hjet g id hm.1 (of_decide_eq_true hm.2))
  simp_rw [he]
  rw [prod_colored_lists ids hn color,hu]
  exact selectedExpressions_readout t ctx.J (codeDigits ctx scalar code) _ marked clause path theta
    ids hn (by simpa using hh) (by simpa using hm)

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
