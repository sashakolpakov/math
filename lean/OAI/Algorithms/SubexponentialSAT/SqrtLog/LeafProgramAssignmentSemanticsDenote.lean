import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsFactors

namespace OAI.Algorithms

/-! Source-scoped semantics of each actual selected factor, followed by the
canonical product in the selected ID order. The marked clause is not lifted
through the hash idempotent. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

noncomputable def indicatorPolynomial (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (H : Squarefree.Jet (Fin n) R) : Squarefree.Jet (Fin n) R :=
  ∑ s : Fin t,
    (Squarefree.Sparse.atom (IdempotentApplyProgram.Multiplier.uKey n) 1)^s.val *
      (IdempotentProgram.digitPolynomial (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        code s).eval₂ ((Moments.ringScalar (V:=Fin n)).comp scalar) H *
      IdempotentProgram.hValue H^s.val

noncomputable def selectedValue (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    Squarefree.Jet (Fin n) R :=
  if h : id < hashes.length then
    indicatorPolynomial ctx scalar code
      (MvPolynomial.eval (jet id) (rowPolynomial (scalarJet (V:=Fin n))
        (sourceTerms (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
          scalar basis) hashes[id])))
  else if marked && decide (id = hashes.length) then
    MvPolynomial.eval (jet id) (clausePolynomial (R := Squarefree.Jet (Fin n) R) clause)
  else 1

theorem indicator_denote (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ v, Good vars ctx.u ctx.J (incidence v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) one = Squarefree.canonical ctx.u ctx.J 1)
    (jet : Fin n → Squarefree.Jet (Fin n) R)
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hjet : ∀ w ∈ ws, ∀ l ∈ w.literals,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence l.variable) = Squarefree.canonical ctx.u ctx.J (jet l.variable))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis)
      (Indicator.result ctx minus one incidence ws (List.ofFn (IdempotentApplyProgram.coefficientTriple t code))) =
      Squarefree.canonical ctx.u ctx.J (indicatorPolynomial ctx scalar code
        (MvPolynomial.eval jet (rowPolynomial (scalarJet (V:=Fin n))
          (sourceTerms (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
            scalar basis) ws)))) := by
  have hh := row_denote_scoped p t ctx.modulus ctx.cache scalar basis ctx.table htable
    vars ctx.u ctx.J minus one incidence hone hi hminus honeval jet ws hjet
  exact IdempotentApplyProgram.applied_coefficients_denote ctx scalar basis htable
    hd hb hu hJ minus hminus _ one hone.nodup honeval _ hh code

/-- Only literals actually read by an ID require the source incidence identity.
Other entries need validity, but need not have any particular denotation. -/
theorem selectedFactor_denote (ctx : Context p t n d)
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
    (hhash : ∀ id (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (hmark : marked=true → ∀ l ∈ clause,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence hashes.length l.variable) =
          Squarefree.canonical ctx.u ctx.J (jet hashes.length l.variable))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (id : ℕ) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
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
        hone (hi id) hminus honeval (jet id) hashes[id] (hhash id h) code
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
          (jet hashes.length) clause (hmark hb')
    · simp [hm] at hfactor

theorem selectedFactor_none_value (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R) (id : ℕ)
    (h : selectedFactor ctx minus one incidence hashes marked clause
      (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)) id = none) :
    selectedValue ctx scalar basis code jet hashes marked clause id = 1 := by
  by_cases hi : id < hashes.length
  · simp only [selectedFactor, hi, dite_true, Option.some_ne_none] at h
  · by_cases hm : (marked && decide (id = hashes.length)) = true
    · simp only [selectedFactor, hi, dite_false, hm, ite_true, Option.some_ne_none] at h
    · simp [selectedValue, hi, hm]

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
