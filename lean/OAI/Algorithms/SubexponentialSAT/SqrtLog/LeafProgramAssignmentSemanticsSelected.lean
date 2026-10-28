import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemantics

namespace OAI.Algorithms

/-! Selected-ID scope sharpening. Unexecuted factors require no source-row
identity; existing all-ID interfaces remain unchanged. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators
variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

/-- Only literals actually read by an ID require the source incidence identity.
Other entries need validity, but need not have any particular denotation. -/
theorem selectedFactor_denote_at (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) one = Squarefree.canonical ctx.u ctx.J 1)
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (id : ℕ)
    (hhash : ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (hmark : marked=true → id=hashes.length → ∀ l ∈ clause,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) =
          Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hfactor : selectedFactor ctx minus one incidence hashes marked clause
      (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)) id = some factor) :
    rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) factor = Squarefree.canonical ctx.u ctx.J
        (selectedValue ctx scalar basis code jet hashes marked clause id) := by
  unfold selectedFactor at hfactor
  by_cases h : id < hashes.length
  · simp only [h, dite_true] at hfactor
    cases hfactor
    simpa only [selectedValue,h,dite_true] using
      indicator_denote ctx scalar basis htable hd hb hu hJ vars minus one (incidence id)
        hone (hi id) hminus honeval (jet id) hashes[id] (hhash h) code
  · simp only [h,dite_false] at hfactor
    by_cases hm : (marked && decide (id=hashes.length)) = true
    · simp only [hm,ite_true] at hfactor
      cases hfactor
      have hp : marked=true ∧ id=hashes.length := by simpa using hm
      have he : id=hashes.length := hp.2
      have hb' : marked=true := hp.1
      subst id
      simpa [selectedValue,h,hb'] using
        clause_list_polynomial_scoped p t ctx.modulus ctx.cache scalar basis ctx.table htable
          vars ctx.u ctx.J minus one (incidence hashes.length) hone hminus honeval
          (jet hashes.length) clause (hmark hb' rfl)
    · simp [hm] at hfactor

theorem selectedRun_polynomial_selected (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi' : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) one = Squarefree.canonical ctx.u ctx.J 1)
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (ids : List ℕ)
    (hhash : ∀ id, id ∈ ids → ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (hmark : hashes.length ∈ ids → marked=true → ∀ l ∈ clause,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence hashes.length l.variable) =
          Squarefree.canonical ctx.u ctx.J (jet hashes.length l.variable))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis)
      (selectedRun ctx.modulus ctx.cache ctx.table ctx.u ctx.J
        (selectedFactor ctx minus one incidence hashes marked clause
          (List.ofFn (IdempotentApplyProgram.coefficientTriple t code))) ids one) =
      Squarefree.canonical ctx.u ctx.J
        ((ids.map (selectedValue ctx scalar basis code jet hashes marked clause)).prod) := by
  have h := selectedRun_denote ctx.modulus ctx.cache scalar basis ctx.table htable ctx.u ctx.J
    (selectedFactor ctx minus one incidence hashes marked clause
      (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)))
    (selectedValue ctx scalar basis code jet hashes marked clause) ids
    (fun id hi factor h => selectedFactor_denote_at ctx scalar basis htable hd hb hu hJ vars
      minus one incidence hone hi' hminus honeval jet hashes marked clause id
      (hhash id hi) (fun hm he => by subst id; exact hmark hi hm) code factor h)
    (fun id _ h => selectedFactor_none_value ctx scalar basis minus one incidence hashes
      marked clause code jet id h) one 1 honeval
  simpa only [one_mul] using h

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
