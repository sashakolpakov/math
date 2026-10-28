import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramExecutionComplete
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramModelCorrectness
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramZero
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramFixed

namespace OAI.Algorithms

/-! The actual native scalar and polynomial programs instantiate every local
service. The remaining hypotheses concern bytes and clean workspace. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram

 def command : Code := localCommand HornerProgram.Services.multiply HornerProgram.Services.add
    Fixed.mulCommand AddService.command

def budget (nodes index q t d J : ℕ) : ℕ :=
  localBudget nodes index (q-2) t J
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (nativeMulBudget J d (baseWidth 3 t))
    (AddService.budget d (baseWidth 3 t) J J)
    (d*baseWidth 3 t) (J*(d*baseWidth 3 t))

theorem command_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (J q : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s scalarWidth frame)
    (hbuffers : ∀ i, s (bufferPorts i) = [])
    (minusOne theta : Coeff (baseWidth 3 t) d) (cs : List (Coeff (baseWidth 3 t) d))
    (jet : Model.Poly (baseWidth 3 t) d J)
    (hzero : s 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hminus : s 211 = RingProgram.flat minusOne) (htheta : s 213 = RingProgram.flat theta)
    (hcs : s 214 = cs.flatMap RingProgram.flat) (hjet : s 225 = Fixed.encode jet)
    (hJ : s 243 = List.replicate J true) (hJcache : (s 193).length = J)
    (hzeroCache : s 192 = DensePolynomialProgram.encode
      (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
    (hexponent : (s 209).length = q-2) (hprecision : (s 212).length = t)
    (hclean : ∀ i ∈ localWork, s i = []) :
    let ops := RingProgram.modelRing t ht hd a M cache
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
        (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) theta minusOne J)
      (Model.constant ops.zeroRun.1 ops.oneRun.1 J)
    ∃ (c : Coeff (baseWidth 3 t) d) (rest : List (Coeff (baseWidth 3 t) d)),
      factor.1 = c :: rest ∧
      ExecutesIn command (budget cs.length (s 216).length q t d J) s
        (Function.update s 244 (Fixed.encode (Model.corrected ops minusOne c q t factor jet))) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
        (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) theta minusOne J)
      (Model.constant ops.zeroRun.1 ops.oneRun.1 J)
  have hz : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth 3 t) false :=
    DensePolynomialProgram.model_zero_bits t a M cache hcanon
  have hsm : ServiceSpec s RingProgram.flat HornerProgram.Services.multiply (Model.scalarMul ops)
      (HornerProgram.Services.mulBudget (baseWidth 3 t) d) :=
    HornerProgram.Services.multiply_spec 3 t M cache hcanon (HornerProgram.modelTable t a M cache) s hscalar
  have hsa : ServiceSpec s RingProgram.flat HornerProgram.Services.add (Model.scalarAdd ops)
      (HornerProgram.Services.addBudget (baseWidth 3 t) d) :=
    HornerProgram.Services.add_spec 3 t M cache (HornerProgram.modelTable t a M cache) s hscalar
  have hpm : ServiceSpec s Fixed.encode Fixed.mulCommand (Fixed.mul ops.program)
      (nativeMulBudget J d (baseWidth 3 t)) :=
    Fixed.mul_spec 3 t M cache ops.program (HornerProgram.modelTable t a M cache) hB hcanon
      (fun _ _ => rfl) (fun _ _ => rfl) s J scalarWidth frame hpoly hbuffers
      (hclean 121 (by simp [localWork])) (hclean 122 (by simp [localWork])) hzeroCache hJcache
  have hpa : ServiceSpec s Fixed.encode AddService.command (Fixed.add ops.program)
      (AddService.budget d (baseWidth 3 t) J J) :=
    Fixed.add_spec 3 t M cache ops.program (HornerProgram.modelTable t a M cache) hB
      (fun _ _ => rfl) s J scalarWidth frame hpoly
  obtain ⟨c,rest,hhead,hbits,hlen⟩ := Model.head_split factor hJpos
  refine ⟨c,rest,hhead,?_⟩
  have h := localCommand_run s RingProgram.flat Fixed.encode
    (fun c => Model.constant ops.zeroRun.1 c J) (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J)
    HornerProgram.Services.multiply HornerProgram.Services.add Fixed.mulCommand AddService.command
    (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program) (Fixed.add ops.program)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J)
    (d*baseWidth 3 t) (J*(d*baseWidth 3 t)) J (Nat.mul_pos hd hB)
    hsm hsa hpm hpa RingProgram.flat_length (fun p => (Fixed.encode_length p).le)
    ops.zeroRun.1 ops.oneRun.1 minusOne theta c cs jet (DensePolynomialProgram.encode rest)
    (fun c => Model.padded_encode ops.zeroRun.1 c ops.zeroRun.1 hz J)
    (fun c => Model.padded_encode ops.zeroRun.1 c ops.oneRun.1 hz J)
    hzero hz hone hminus htheta hcs hJ hjet
    (by
      rw [Model.constant_zero]
      change s 192 = Fixed.encode (Model.zero
        (RingProgram.modelProgram t a M cache).zeroRun.1 J)
      simpa only [Fixed.encode, Model.zero] using hzeroCache)
    hclean (fun _ => hbits)
  simpa only [command, budget, hexponent, hprecision, ite_eq_right (Nat.ne_of_gt hJpos),
    Model.corrected, Model.inverseCoefficient, Model.constant_zero] using h

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Native

end OAI.Algorithms
