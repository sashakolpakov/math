import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsDenote
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemantics

namespace OAI.Algorithms

/-! The assignment output is a pair, as in the actual native callback: the
Boolean coefficient is separate from the raw factor fold. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

 theorem selectedRun_polynomial (ctx : Context p t n d)
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
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (ids : List ℕ) :
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
    (fun id _ factor h => selectedFactor_denote ctx scalar basis htable hd hb hu hJ vars
      minus one incidence hone hi hminus honeval jet hashes marked clause hhash hmark code id factor h)
    (fun id _ h => selectedFactor_none_value ctx scalar basis minus one incidence hashes
      marked clause code jet id h) one 1 honeval
  simpa only [one_mul] using h

def coefficient (zero one : RingProgram.Code (Word (baseWidth p t)) d)
    (assignment support headMask : List Bool) : RingProgram.Code (Word (baseWidth p t)) d :=
  if LeafWeightProgram.good assignment support headMask then one else zero

omit [Fact (Nat.Prime p)] in
theorem coefficient_bytes (zero one : RingProgram.Code (Word (baseWidth p t)) d)
    (assignment support headMask : List Bool) :
    RingProgram.flat (coefficient zero one assignment support headMask) =
      LeafWeightProgram.Native.result assignment support headMask
        (RingProgram.flat zero) (RingProgram.flat one) := by
  unfold coefficient LeafWeightProgram.Native.result
  split <;> rfl

def contribution (ctx : Context p t n d)
    (zeroCoeff oneCoeff : RingProgram.Code (Word (baseWidth p t)) d)
    (assignment support headMask : List Bool)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)))
    (ids : List ℕ) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : MomentsAssembly.Contribution n (baseWidth p t) d :=
  (coefficient zeroCoeff oneCoeff assignment support headMask,
    selectedRun ctx.modulus ctx.cache ctx.table ctx.u ctx.J select ids one)

 theorem contribution_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (zeroCoeff oneCoeff : RingProgram.Code (Word (baseWidth p t)) d)
    (assignment support headMask : List Bool)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)))
    (ids : List ℕ) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hselect : ∀ id ∈ ids, ∀ factor, select id = some factor → Good vars ctx.u ctx.J factor) :
    Good vars ctx.u ctx.J
      (contribution ctx zeroCoeff oneCoeff assignment support headMask select ids one).2 :=
  selectedRun_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J select ids hselect one hone

/-- This exact product can be discharged by selectedRun_polynomial above.
The Boolean weight uses the current head assignment, not its merged baseline. -/
theorem contribution_denote (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (zeroCoeff oneCoeff : RingProgram.Code (Word (baseWidth p t)) d)
    (hzero : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis zeroCoeff = 0)
    (honeCoeff : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis oneCoeff = 1)
    {G : Type*} [Fintype G] [DecidableEq G]
    (assignment : Fin n → Bool) (support : Squarefree.Support (Fin n))
    (head : Fin n → G) (g : G)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)))
    (ids : List ℕ) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (value : ℕ → Squarefree.Jet (Fin n) R)
    (hproduct : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) (selectedRun ctx.modulus ctx.cache ctx.table ctx.u ctx.J select ids one) =
      Squarefree.canonical ctx.u ctx.J ((ids.map value).prod)) :
    MomentsAssembly.contributionDenote p t ctx.modulus ctx.cache scalar basis
      (contribution ctx zeroCoeff oneCoeff (List.ofFn assignment)
        (LeafWeightProgram.supportBits support) (LeafWeightProgram.headBits head g) select ids one) =
      Moments.ringScalar (Moments.localBoolWeight head support g (fun i => assignment i.val)) *
        Squarefree.canonical ctx.u ctx.J ((ids.map value).prod) := by
  have hw : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis
      (coefficient zeroCoeff oneCoeff (List.ofFn assignment)
        (LeafWeightProgram.supportBits support) (LeafWeightProgram.headBits head g)) =
      Moments.localBoolWeight head support g (fun i => assignment i.val) := by
    rw [← LeafWeightProgram.localBoolWeight_eq assignment support head g]
    unfold coefficient
    split <;> assumption
  exact MomentsAssembly.contributionDenote_eq p t ctx.modulus ctx.cache scalar basis
    _ _ _ hw hproduct

/-- Boolean scaling commutes with the canonical projection without any
unproved multiplicativity claim for general truncations. -/
theorem boolean_scalar_canonical (u J : ℕ) (b : Bool)
    (P : Squarefree.Jet (Fin n) R) :
    Moments.ringScalar (if b then (1:R) else 0) * Squarefree.canonical u J P =
      Squarefree.canonical u J (Moments.ringScalar (if b then (1:R) else 0) * P) := by
  cases b <;> simp

/-- The weighted head contribution is itself one canonical product. -/
theorem localWeight_canonical {G : Type*} [Fintype G] [DecidableEq G]
    (u J : ℕ) (assignment : Fin n → Bool) (support : Squarefree.Support (Fin n))
    (head : Fin n → G) (g : G) (P : Squarefree.Jet (Fin n) R) :
    Moments.ringScalar (Moments.localBoolWeight head support g (fun i => assignment i.val)) *
        Squarefree.canonical u J P =
      Squarefree.canonical u J
        (Moments.ringScalar (Moments.localBoolWeight head support g (fun i => assignment i.val)) * P) := by
  rw [← LeafWeightProgram.localBoolWeight_eq assignment support head g]
  exact boolean_scalar_canonical u J _ P

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
