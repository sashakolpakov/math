import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramBoundsPolynomial

namespace OAI.Algorithms

/-! Bounds for the measured native factor services and their paid cleanup.
The retained-key capacity remains an explicit argument of every envelope. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps NativeSemantics

def tableBound (B d n u J N : ℕ) : ℕ :=
  n*(2*n+2*Cost.bytesBound B d n u J N+2)

def hashServiceBound (B d n u J N k m L : ℕ) : ℕ :=
  Cost.programBound B d n u J N k m+
    IdempotentApplyProgram.Bounds.totalEnvelope B d n u J N L+
    58*Cost.bytesBound B d n u J N+2*tableBound B d n u J N+
    Cost.productBound B d n u J N+64

def markedServiceBound (B d n u J N k : ℕ) : ℕ :=
  k*(6*(2*n+1)+Cost.literalBound B d n u J N+7)+
    63*Cost.bytesBound B d n u J N+2*tableBound B d n u J N+
    Cost.productBound B d n u J N+66

theorem indicator_good_iff {n B d u J : ℕ} {vars : Finset (Fin n)}
    {a : List (Product.Entry n B d)} :
    IdempotentApplyProgram.Bounds.Good vars u J a ↔ Good vars u J a :=
  ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.valid,h.nodup⟩⟩

variable {p t n d : ℕ} [Fact p.Prime]

theorem rawHash_good (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good Finset.univ ctx.u ctx.J one)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d)) :
    Good Finset.univ ctx.u ctx.J (Indicator.rawHash ctx minus one incidence ws) :=
  row_fold_good p t ctx.modulus ctx.cache ctx.table Finset.univ ctx.u ctx.J
    minus one incidence hone hi ws [] Good.nil

theorem result_good (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good Finset.univ ctx.u ctx.J one)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) :
    Good Finset.univ ctx.u ctx.J (Indicator.result ctx minus one incidence ws digits) := by
  have hh := rawHash_good ctx minus one incidence hone hi ws
  have hp := IdempotentApplyProgram.Bounds.prepared_bounded ctx Finset.univ minus
    (Indicator.rawHash ctx minus one incidence ws) one hh.valid (indicator_good_iff.mpr hone)
  exact indicator_good_iff.mp (IdempotentApplyProgram.Bounds.loopResult_good ctx Finset.univ
    hu hJ _ _ hh.valid hp.1 digits.reverse []
      (IdempotentApplyProgram.Bounds.good_nil Finset.univ ctx.u ctx.J))

omit [Fact (Nat.Prime p)] in
theorem table_length (ctx : Context p t n d)
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v)) :
    (Squarefree.Program.lookupRecords (Cost.entries incidence)).length ≤
      tableBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J) := by
  have hp := fun v => Cost.good_bytes (hi v) (le_refl
    (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J))
  simpa only [Cost.entries,LookupBounds.incidence_entries_length,tableBound] using
    LookupBounds.records_length (Cost.entries incidence) n _
      (LookupBounds.incidence_key_length _ ())
      (LookupBounds.incidence_payload_length _ () _ hp)

theorem productBudget_le (ctx : Context p t n d)
    (seed factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hs : Good Finset.univ ctx.u ctx.J seed)
    (hf : Good Finset.univ ctx.u ctx.J factor) :
    Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor ≤
      56*Cost.bytesBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J)+
      Cost.productBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J)+54 := by
  have hcap := le_refl (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J)
  have bs := Cost.good_bytes hs hcap
  have bf := Cost.good_bytes hf hcap
  have br := Cost.good_bytes (product_good p t ctx.modulus ctx.cache ctx.table
    Finset.univ ctx.u ctx.J seed factor hs hf) hcap
  have hw := Cost.product_le p t ctx.modulus ctx.cache ctx.table hcap seed factor hs hf
  dsimp only [Factor.productBudget]
  omega

theorem indicatorBudget_le (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good Finset.univ ctx.u ctx.J one)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits ≤
      Cost.programBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J) k ws.length+
      IdempotentApplyProgram.Bounds.totalEnvelope (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J) digits.length+4 := by
  have hh := rawHash_good ctx minus one incidence hone hi ws
  have hc := Cost.program_le p t ctx.modulus ctx.cache ctx.table
    (le_refl (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J))
    minus one incidence hone hi (List.replicate d true) (by simp) ws k hk
  have ha := IdempotentApplyProgram.Bounds.totalCost_le ctx Finset.univ hu hJ minus
    (Indicator.rawHash ctx minus one incidence ws) one
    (IdempotentApplyProgram.Bounds.good_bounded ctx Finset.univ _ (indicator_good_iff.mpr hh))
    (indicator_good_iff.mpr hone) digits
  change IdempotentApplyProgram.applicationBudget _ _ _ _ _ ≤ _ at ha
  unfold FactorServices.indicatorBudget
  omega

theorem hashService_le (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good Finset.univ ctx.u ctx.J one) (hs : Good Finset.univ ctx.u ctx.J seed)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits+
      (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
        2*(Squarefree.Program.lookupRecords (Cost.entries incidence)).length+6+
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence ws digits)) ≤
      hashServiceBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J) k ws.length digits.length := by
  have h1 := indicatorBudget_le ctx hu hJ minus one incidence hone hi ws digits k hk
  have h2 := table_length ctx incidence hi
  have h3 := Cost.good_bytes (rawHash_good ctx minus one incidence hone hi ws)
    (le_refl (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J))
  have h4 := productBudget_le ctx seed _ hs (result_good ctx hu hJ minus one incidence hone hi ws digits)
  unfold hashServiceBound
  omega

theorem clauseResult_good (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good Finset.univ ctx.u ctx.J one)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    Good Finset.univ ctx.u ctx.J (FactorServices.clauseResult ctx minus one incidence ls) :=
  clause_fold_good p t ctx.modulus ctx.cache ctx.table Finset.univ ctx.u ctx.J
    minus one incidence hone hi ls one hone

theorem markedService_le (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good Finset.univ ctx.u ctx.J one) (hs : Good Finset.univ ctx.u ctx.J seed)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    FactorServices.clauseBudget ctx minus one incidence (Cost.entries incidence) ls+
      (2*(Squarefree.Program.lookupRecords (Cost.entries incidence)).length+3+
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (FactorServices.clauseResult ctx minus one incidence ls)) ≤
      markedServiceBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J) ls.length := by
  have h1 := Cost.clause_le p t ctx.modulus ctx.cache ctx.table
    (le_refl (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J))
    minus one incidence hone hi (List.replicate d true) (by simp) ls one hone
  have h2 := table_length ctx incidence hi
  have h3 := Cost.good_bytes hone
    (le_refl (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J))
  have h4 := productBudget_le ctx seed _ hs (clauseResult_good ctx minus one incidence hone hi ls)
  unfold FactorServices.clauseBudget markedServiceBound
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
