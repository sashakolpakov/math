import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramFixedBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops

namespace OAI.Algorithms

/-! Fixed-length coefficient-array carriers for the local CRT/Horner loops.
The multiplication service obtains its zero array and length from protected
caches192/193. The relocation is in the finite instruction table, so no tape
copy is charged or hidden by the change of physical port names. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod


def relocation : Fin 256 ≃ Fin 256 :=
  (Equiv.swap 242 192).trans (Equiv.swap 243 193)
def ports : Fin 256 ↪ Fin 256 := relocation.toEmbedding

def mulCommand : Code := .call (ProgramLinking.liftProgram nativeMulProgram id ports)

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

omit [Fact (Nat.Prime p)] in
private theorem ready_frame (base s : Store) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table base scalarWidth frame)
    (hf : CRTLocalProgram.LowFrame base s) :
    PairSpec.BaseReady p t M cache table (s ∘ ports) scalarWidth frame := by
  apply PairSpec.BaseReady.frame_except_caches p t M cache table H
  intro i hi h192 h193
  have h242 : i ≠ 242 := by intro h; subst i; norm_num at hi
  have h243 : i ≠ 243 := by intro h; subst i; norm_num at hi
  simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,h192,h193,h242,h243]
    using hf i hi

/-- No high cache invariant is assumed by the service: only the protected
low workspace, encoded operands, and its two empty output buffers. -/
theorem mul_spec (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (base : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table base scalarWidth frame)
    (hempty : ∀ i, base (bufferPorts i) = [])
    (h121 : base 121 = []) (h122 : base 122 = [])
    (hzero : base 192 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1))
    (hJ : (base 193).length = J) :
    CRTLocalProgram.ServiceSpec base (encode (J:=J)) mulCommand (mul ops)
      (nativeMulBudget J degree (baseWidth p t)) := by
  intro s P Q hf hP hQ h244 h245 regs
  have Hs := ready_frame p t M cache table base s scalarWidth frame H hf
  have he : ∀ i, (s ∘ ports) (bufferPorts i) = [] := by
    intro i
    have hh := hf (bufferPorts i) (by fin_cases i <;> decide)
    have hh2 := hempty i
    fin_cases i <;> simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,bufferPorts] using hh.trans hh2
  have hz' : (s ∘ ports) 242 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1) := by
    simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using (hf 192 (by decide)).trans hzero
  have hJ' : ((s ∘ ports) 243).length = J := by
    simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,hf 193 (by decide)] using hJ
  obtain ⟨n,hn,rf,ht⟩ := native_mul_trace p t M cache ops table hB hz hadd hmul
    (s ∘ ports) J P.1 Q.1 scalarWidth frame Hs he
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using (hf 121 (by decide)).trans h121)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using (hf 122 (by decide)).trans h122)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using h244)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using h245)
    P.2 Q.2
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,encode] using hP)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,encode] using hQ) hz' hJ' regs
  let d : Data := ⟨regs,s⟩
  have hc := eval_call_from_state nativeMulProgram id ports d Function.injective_id ports.injective ht
  have hext : Function.extend ports (s ∘ ports) s = s :=
    congrArg StructuredProgram.State.stacks (embedState_project id ports d Function.injective_id ports.injective)
  have hout : (embedState id ports d
      (⟨rf,Function.update (s ∘ ports) 244 (DensePolynomialProgram.encode (result ops J P.1 Q.1))⟩ : Data)).stacks =
      Function.update s 244 (encode (mul ops P Q)) := by
    change Function.extend ports _ s = _
    rw [ProgramLinking.extend_update ports.injective,hext]
    rfl
  let final := embedState id ports d
    (⟨rf,Function.update (s ∘ ports) 244 (DensePolynomialProgram.encode (result ops J P.1 Q.1))⟩ : Data)
  have heq : final = (⟨final.regs,Function.update s 244 (encode (mul ops P Q))⟩ : Data) :=
    SubexponentialSAT.SubexpScanPrimitives.state_ext rfl hout
  refine ⟨n,final.regs,hn,?_⟩
  change Eval mulCommand n d final at hc
  rw [heq] at hc
  exact hc


/-- The fixed-length addition instance uses the same restored native frame. -/
theorem add_spec (hB : 0 < baseWidth p t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (base : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table base scalarWidth frame) :
    CRTLocalProgram.ServiceSpec base (encode (J:=J)) AddService.command (add ops)
      (AddService.budget degree (baseWidth p t) J J) := by
  intro s P Q hf hP hQ h244 h245
  have hs : ∀ i, s (SubexponentialSAT.SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] scalarWidth [] frame).stacks i := by
    intro i
    have hi := H.low i
    have hh := hf (SubexponentialSAT.SubexpPolynomialAddService.ports i)
      (by dsimp [SubexponentialSAT.SubexpPolynomialAddService.ports]; omega)
    exact hh.trans hi
  have h := AddService.command_value p t M cache s hB ops hadd P.1 Q.1 scalarWidth frame
    H.scalarWidthLength hs ((hf 120 (by decide)).trans H.scratch) h244 h245 hP hQ
  simpa only [encode, add, P.2, Q.2] using h

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
