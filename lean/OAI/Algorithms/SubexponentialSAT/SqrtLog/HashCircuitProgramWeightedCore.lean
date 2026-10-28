import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProduct

namespace OAI.Algorithms

/-! Shared native weighted sparse accumulation. This local56-stack core is
used by hash rows and head moments. It retains the source dictionary41,
consumes the flat coefficient44, and replaces accumulator42 by the normalized
weighted sum. Its output restores all temporary work used by these phases. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- Both subphases are concrete fixed bit programs. -/
abbrev command : Cmd 8 56 :=
  .seq Product.scalePhase
    (.seq (Product.copy 38 4) (.seq (Product.clear 38) Product.normalizePhase))
def program := compiled command 41 42

theorem copyScaled_eval (regs : Fin 8 → Bool) (a : Product.Store) (h : a.mapped = []) :
    Eval (Product.copy 38 4) (7*a.scaled.length+5) (Product.state regs a)
      (Product.state (readRegs regs 0 1 none) {a with mapped := a.scaled}) := by
  apply Product.copy_state regs a {a with mapped := a.scaled} 38 4
    (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [Product.tapes,StackRoutines.copyStacks,h]

theorem clearScaled_eval (regs : Fin 8 → Bool) (a : Product.Store) :
    Eval (Product.clear 38) (2*a.scaled.length+3) (Product.state regs a)
      (Product.state (readRegs regs 0 1 none) {a with scaled := []}) := by
  apply Product.clear_state regs a {a with scaled := []} 38
  funext i; fin_cases i <;> simp [Product.tapes,StackRoutines.clearStacks]

variable {K : Type*} [DecidableEq K]

theorem command_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (hk : Function.Injective key)
    (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Product.Store)
    (he : Product.scaleEnvironment a a.coeff = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
    (hm : a.modulus = M.bits) (hwidth : a.width = width) (hdegree : a.degree = degree)
    (hr : a.right = Squarefree.ScaleProgram.encode key entries)
    (hseed : a.acc = Normalize.bytes key seed)
    (hs : a.scaleSource = []) (hc : a.scalar = []) (ho : a.scaled = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = [])
    (h51 : a.normalCount = []) :
    let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
    ∃ n ≤ 25*a.right.length+11*a.coeff.length+9*a.degree.length+
      Squarefree.ScaleProgram.budget key entries + Normalize.work p t M cache key weighted seed+43,
      ∃ rr, Eval command n (Product.state regs a)
        (Product.state rr {a with coeff := [], acc := Normalize.bytes key (Normalize.run p t M cache weighted seed)}) := by
  dsimp only
  let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
  let output := Squarefree.ScaleProgram.encode key weighted
  let b : Product.Store := {a with coeff := [],scaled := output}
  let c : Product.Store := {b with mapped := output}
  let e : Product.Store := {c with scaled := []}
  obtain ⟨n,hn,r1,hscale⟩ := Product.scalePhase_eval p t M cache hz table scalar degree width hd hw
    key entries regs a he hr hs hc ho h0 h1 h2 h3 h4 h27
  have hcopy := copyScaled_eval r1 b (by simpa [b] using h4)
  have hclear := clearScaled_eval (readRegs r1 0 1 none) c
  obtain ⟨m,hmb,r2,hnorm⟩ := Product.normalizePhase_eval p t M cache key hk weighted seed
    (readRegs (readRegs r1 0 1 none) 0 1 none) e
    (by simpa [e,c,b] using hm)
    (by simpa [e,c,b,hwidth] using hw)
    (by simpa [e,c,b,hdegree] using hd)
    (by rfl) (by simpa [e,c,b] using hseed)
    (by simpa [e,c,b] using h27) (by simpa [e,c,b] using h51)
    (by simpa [e,c,b] using h0) (by simpa [e,c,b] using h1)
    (by simpa [e,c,b] using h2) (by simpa [e,c,b] using h3)
  have hlen : output.length = a.right.length := by
    rw [hr]
    exact Squarefree.ScaleProgram.encode_scaled_length p t M cache table scalar key entries
  have hrun := hscale.seq (hcopy.seq (hclear.seq hnorm))
  refine ⟨n+(7*output.length+5)+ (2*output.length+3)+m,?_,r2,?_⟩
  · dsimp only [b,c,e,weighted] at hn hmb ⊢
    rw [hlen] at hmb ⊢
    omega
  · convert hrun using 1
    · dsimp only [b,c]
      omega
    · apply congrArg (Product.state r2)
      cases a
      simp_all [b,c,e,weighted]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore

end OAI.Algorithms
