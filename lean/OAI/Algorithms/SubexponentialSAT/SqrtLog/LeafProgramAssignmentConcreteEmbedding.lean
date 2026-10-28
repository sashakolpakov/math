import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcreteAdmissible
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingMoments

namespace OAI.Algorithms

/-! Selected factors may have ambient literal IDs but free formal variables.
Embedding is performed on the polynomial itself, never through a chosen
stored representation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree NodeSemantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators

variable {V W I R : Type*} [DecidableEq V] [DecidableEq W] [CommRing R]

theorem indicatorJet_embedding (e : V ↪ W) (t : ℕ) (digits : Fin t → R[X])
    (F : Jet V R) :
    ResidualEmbedding.jet e (indicatorJet t digits F) =
      indicatorJet t digits (ResidualEmbedding.jet e F) := by
  unfold indicatorJet
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hc : (ResidualEmbedding.jet (R:=R) e).comp Moments.ringScalar =
      Moments.ringScalar := by
    apply RingHom.ext
    intro c
    exact ResidualEmbedding.jet_ringScalar e c
  have he := Polynomial.hom_eval₂ (digits s) Moments.ringScalar (ResidualEmbedding.jet e) F
  rw [hc] at he
  have hu : ResidualEmbedding.jet e (Polynomial.X : Jet V R) = Polynomial.X := by
    simp [ResidualEmbedding.jet]
  have hh : ResidualEmbedding.jet e (IdempotentProgram.hValue F) =
      IdempotentProgram.hValue (ResidualEmbedding.jet e F) := by
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat]
  simp only [map_mul,map_pow,hu,he,hh]

theorem clause_source_embedding (e : V ↪ W) (value : I → Jet V R)
    (ls : List (SAT.Literal I)) :
    MvPolynomial.eval (fun i => ResidualEmbedding.jet e (value i))
      (clausePolynomial (R:=Jet W R) ls) =
    ResidualEmbedding.jet e (MvPolynomial.eval value (clausePolynomial (R:=Jet V R) ls)) := by
  have h := map_clauseValue (V:=I) (R:=Jet V R) (S:=Jet W R) (ResidualEmbedding.jet e) value ls
  simpa only [clauseValue_eq_eval] using h.symm

variable {p t n d : ℕ} [Fact p.Prime]

def residualValue (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) : Jet V R :=
  if h : id < hashes.length then
    indicatorJet t (codeDigits ctx scalar code)
      (MvPolynomial.eval (jfree id) (rowPolynomial (R:=Jet V R) scalarJet
        (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
          hashes[id])))
  else if marked && decide (id=hashes.length) then
    MvPolynomial.eval (jfree id) (clausePolynomial (R:=Jet V R) clause)
  else 1

theorem selectedValue_embedding (e : V ↪ Fin n) (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (jamb : ℕ → Fin n → Jet (Fin n) R)
    (hj : ∀ id v, jamb id v=ResidualEmbedding.jet e (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    AssignmentSemantics.selectedValue ctx scalar basis code jamb hashes marked clause id =
      ResidualEmbedding.jet e (residualValue ctx scalar basis code jfree hashes marked clause id) := by
  have he : jamb = fun id v => ResidualEmbedding.jet e (jfree id v) := by
    funext id v
    exact hj id v
  rw [he]
  unfold AssignmentSemantics.selectedValue residualValue
  by_cases h : id < hashes.length
  · simp only [dite_eq_left h]
    rw [indicatorPolynomial_eq,ResidualEmbedding.row_source_jet,← indicatorJet_embedding]
  · simp only [dite_eq_right h]
    split
    · exact clause_source_embedding e (jfree id) clause
    · exact (map_one (ResidualEmbedding.jet e)).symm

theorem residualValue_admissible (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (hj : ∀ id v, Admissible (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    Admissible (residualValue ctx scalar basis code jfree hashes marked clause id) := by
  unfold residualValue
  split
  · apply admissible_indicatorJet
    rw [← rowValue_eq_eval (R:=Jet V R) (scalarJet (V:=V)) (jfree id)]
    exact admissible_row (jfree id) (hj id) _
  · split
    · rw [← clauseValue_eq_eval (R:=Jet V R) (jfree id) clause]
      exact admissible_clause (jfree id) (hj id) clause
    · exact admissible_one

theorem canonical_product_embedding (e : V ↪ Fin n) (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (jamb : ℕ → Fin n → Jet (Fin n) R)
    (hj : ∀ id v, jamb id v=ResidualEmbedding.jet e (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ) :
    canonical ctx.u ctx.J
      ((ids.map (AssignmentSemantics.selectedValue ctx scalar basis code jamb hashes marked clause)).prod) =
    ResidualEmbedding.jet e (canonical ctx.u ctx.J
      ((ids.map (residualValue ctx scalar basis code jfree hashes marked clause)).prod)) := by
  rw [ResidualEmbedding.jet_canonical]
  congr 1
  rw [map_list_prod (ResidualEmbedding.jet e)]
  apply congrArg List.prod
  rw [List.map_map]
  apply List.map_congr_left
  intro id hi
  exact selectedValue_embedding e ctx scalar basis code jfree jamb hj hashes marked clause id

theorem residual_product_admissible (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (hj : ∀ id v, Admissible (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ) :
    Admissible (canonical ctx.u ctx.J
      ((ids.map (residualValue ctx scalar basis code jfree hashes marked clause)).prod)) := by
  apply Admissible.canonical
  apply admissible_list_prod
  intro id hi
  exact residualValue_admissible ctx scalar basis code jfree hj hashes marked clause id

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
