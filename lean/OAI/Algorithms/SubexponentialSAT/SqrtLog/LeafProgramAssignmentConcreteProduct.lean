import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcreteScoped
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsProduct

namespace OAI.Algorithms

/-! The common query product requires source equality only on actually read
literals of selected factors.  Unused source coordinates are unrestricted. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps (Context)
open NodeSemantics AssignmentSemantics
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem colored_products_query_scoped {p t n d : ℕ} [Fact p.Prime]
    (ctx : Context p t n d) (hu : ctx.u=t)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    {G : Type*} [Fintype G] [DecidableEq G]
    (ids : List ℕ) (hn : ids.Nodup) (color : ℕ → G)
    (jet : G → ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (D : G → Squarefree.Jet (Fin n) R)
    (path : ℕ → Fin n → R[X]) (theta : R)
    (x : Fin n → R) (hx : ∀ v, x v*x v=x v)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (hhash : ∀ g id, id∈ids → color id=g → ∀ (hi : id < hashes.length),
      ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
        Moments.jetEval x hx (jet g id l.variable)=
          Polynomial.C (shift theta (path id l.variable)))
    (hmark : ∀ g, marked=true → hashes.length∈ids → color hashes.length=g →
      ∀ l ∈ clause, Moments.jetEval x hx (jet g hashes.length l.variable)=
        Polynomial.C (shift theta (path hashes.length l.variable)))
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
    have hp := List.mem_filter.mp hi
    have hc : color id=g := of_decide_eq_true hp.2
    apply selectedValue_eval_scoped ctx scalar basis code (jet g) _ x hx hashes marked clause id
    · exact hhash g id hp.1 hc
    · intro hm' heq
      subst id
      exact hmark g hm' hp.1 hc
  simp_rw [he]
  rw [prod_colored_lists ids hn color,hu]
  exact selectedExpressions_readout t ctx.J (codeDigits ctx scalar code) _ marked clause path theta
    ids hn (by simpa using hh) (by simpa using hm)

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
