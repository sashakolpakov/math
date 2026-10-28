import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramMultiplierKernel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramExecution

namespace OAI.Algorithms

/-! Full native application of a computed idempotent coefficient array.
The multiplier is built from H and ordinary cached constants; the indicator
is then computed by the measured Horner loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def applied (ctx : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  loopResult ctx h (Multiplier.prepared ctx minus h one) vs.reverse []

def applicationBudget (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) : ℕ :=
  Multiplier.prepareCost ctx minus h one+
    applyLoopCost ctx h (Multiplier.prepared ctx minus h one) vs
      (Squarefree.encodeIndex (Multiplier.uKey n))+1

/-- No desired polynomial is supplied to the command: only H, scalar constants,
and the computed base-coefficient tape occur in the initial memory contract. -/
theorem command_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (htape : high 22=triplesTape vs)
    (h23 : high 23=[]) (hshape : (high 32).length=n) (hready : Multiplier.ready high) :
    ∃ cost, cost+1 ≤ applicationBudget ctx minus h one vs ∧ ∃ rr,
      Eval command cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx) (Function.update high 11 (Product.bytes (applied ctx minus h one vs)))) := by
  obtain ⟨kp,bp,rp,ep⟩:=Multiplier.prepareMultiplier_eval ctx minus h one regs high hh ho hm hshape hready
  let prepared:=Multiplier.prepared ctx minus h one
  let mid:=Function.update (Function.update high (38:Fin 40)
    (Squarefree.encodeIndex (Multiplier.uKey n))) 30 (Product.bytes prepared)
  have rmid : scalarReady 11 mid := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false]
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply hready <;> simp
  obtain ⟨kl,bl,rl,el⟩:=applyLoop_eval ctx hd hB h prepared vs rp mid
    (by simpa [mid] using hh) (by simp [mid])
    (by simpa [mid] using htape) (by simpa [mid] using hready 5 (by simp))
    (by simpa [mid] using h23) (by simpa [mid] using hready 28 (by simp))
    (by simpa [mid] using hready 29 (by simp))
    (by simpa [mid] using hready 31 (by simp))
    (by simpa [mid] using hshape) rmid
  have hout : Function.update (Function.update (Function.update mid 30 []) 38 []) 11
      (Product.bytes (loopResult ctx h prepared vs.reverse []))=
      Function.update high 11 (Product.bytes (applied ctx minus h one vs)) := by
    have h30:=hready 30 (by simp)
    have h38:=hready 38 (by simp)
    funext i
    by_cases hi : i=30 <;> by_cases hj : i=38 <;> by_cases hk : i=11 <;>
      simp_all [mid,applied,prepared,Function.update_apply]
  rw [hout] at el
  refine ⟨kp+kl,?_,rl,ep.seq el⟩
  have hkey : mid 38=Squarefree.encodeIndex (Multiplier.uKey n):=by simp [mid]
  rw [hkey] at bl
  dsimp [applicationBudget,prepared] at bp bl ⊢
  omega

theorem program_runs (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (htape : high 22=triplesTape vs)
    (h23 : high 23=[]) (hshape : (high 32).length=n) (hready : Multiplier.ready high) :
    ∃ rr, RunsIn program (applicationBudget ctx minus h one vs)
      ((Memory.state regs (low ctx) high).withPC (some program.entry))
      ((Memory.state rr (low ctx) (Function.update high 11
        (Product.bytes (applied ctx minus h one vs)))).withPC none) := by
  obtain ⟨cost,hcost,rr,he⟩:=command_eval ctx hd hB minus h one vs regs high hh ho hm htape h23 hshape hready
  exact ⟨rr,cost+1,hcost,compiled_halt_trace he 68 67⟩

variable {R : Type*} [CommRing R]

/-- Exact semantics of the bytes produced by the native application command. -/
theorem applied_coefficients_denote (ctx : Context p t n d)
    (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hj : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) φ basis minus = -1)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (honeKeys : (Squarefree.Sparse.keys one).Nodup)
    (hone : storedDenote p t ctx.modulus ctx.cache φ basis one=Squarefree.canonical ctx.u ctx.J 1)
    (H : Squarefree.Jet (Fin n) R)
    (hh : storedDenote p t ctx.modulus ctx.cache φ basis h=Squarefree.canonical ctx.u ctx.J H)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    storedDenote p t ctx.modulus ctx.cache φ basis
      (applied ctx minus h one (List.ofFn (coefficientTriple t code)))=
      Squarefree.canonical ctx.u ctx.J (∑ s : Fin t,
        (Squarefree.Sparse.atom (Multiplier.uKey n) 1)^s.val *
          (IdempotentProgram.digitPolynomial (RingProgram.scalarRing p t ctx.modulus ctx.cache)
            code s).eval₂ ((Moments.ringScalar (V:=Fin n)).comp φ) H *
          IdempotentProgram.hValue H^s.val) := by
  unfold applied
  rw [loopResult_eq]
  exact applyStored_denote p t ctx.modulus ctx.cache φ basis ctx.table htable hd hb ctx.u ctx.J hu hj
    h (Multiplier.prepared ctx minus h one) H (Squarefree.Sparse.atom (Multiplier.uKey n) 1) hh
    (Multiplier.prepared_denote ctx φ basis htable minus hminus h one honeKeys hone H hh) code


/-- The fixed native program consumes the concrete array computed by the lift
and returns the stored indicator polynomial with the stated exact meaning. -/
theorem program_coefficients (ctx : Context p t n d)
    (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hB : 0 < baseWidth p t) (hb : basis ⟨0,hd⟩=1)
    (hu : 0 < ctx.u) (hj : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) φ basis minus = -1)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (honeKeys : (Squarefree.Sparse.keys one).Nodup)
    (hone : storedDenote p t ctx.modulus ctx.cache φ basis one=Squarefree.canonical ctx.u ctx.J 1)
    (H : Squarefree.Jet (Fin n) R)
    (hH : storedDenote p t ctx.modulus ctx.cache φ basis h=Squarefree.canonical ctx.u ctx.J H)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (hcode : high 22=RingProgram.flat code)
    (h23 : high 23=[]) (hshape : (high 32).length=n) (hready : Multiplier.ready high) :
    let vs:=List.ofFn (coefficientTriple t code)
    ∃ rr, RunsIn program (applicationBudget ctx minus h one vs)
      ((Memory.state regs (low ctx) high).withPC (some program.entry))
      ((Memory.state rr (low ctx) (Function.update high 11
        (Product.bytes (applied ctx minus h one vs)))).withPC none) ∧
      storedDenote p t ctx.modulus ctx.cache φ basis (applied ctx minus h one vs)=
        Squarefree.canonical ctx.u ctx.J (∑ s : Fin t,
          (Squarefree.Sparse.atom (Multiplier.uKey n) 1)^s.val *
            (IdempotentProgram.digitPolynomial (RingProgram.scalarRing p t ctx.modulus ctx.cache)
              code s).eval₂ ((Moments.ringScalar (V:=Fin n)).comp φ) H *
            IdempotentProgram.hValue H^s.val) := by
  dsimp only
  obtain ⟨rr,hr⟩:=program_runs ctx hd hB minus h one (List.ofFn (coefficientTriple t code))
    regs high hh ho hm (by simpa only [coefficient_tape] using hcode) h23 hshape hready
  exact ⟨rr,hr,applied_coefficients_denote ctx φ basis htable hd hb hu hj minus hminus
    h one honeKeys hone H hH code⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
