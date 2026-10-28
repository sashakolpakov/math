import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyShift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramHorner
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramFixed

namespace OAI.Algorithms

/-! The actual fixed-length polynomial services instantiate the shifted-row
machine. Its semantic result follows from the executed Horner fold. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev shiftedValue {B d : ℕ} (ops : RingProgram (Coeff B d))
    (J : ℕ) (theta : Coeff B d) (P : List (Coeff B d)) : Fixed.Array B d J :=
  HornerProgram.fold (HornerProgram.stepValue (Fixed.mul ops) (Fixed.add ops)
    (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (P.map (fun c => CRTLocalProgram.Model.constant ops.zeroRun.1 c J)).reverse
    (CRTLocalProgram.Model.zero ops.zeroRun.1 J)

theorem shiftedValue_denote {B d : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (J : ℕ) (theta : Coeff B d)
    (P : List (Coeff B d)) :
    CRTLocalProgram.Model.denote ops.decode (shiftedValue ops.program J theta P) =
      Truncation.trunc J ((PolynomialAlgorithm.denote (P.map ops.decode)).comp
        (Polynomial.X+Polynomial.C (ops.decode theta))) := by
  exact PerturbationProgram.shifted_horner_denote J ops.decode
    (CRTLocalProgram.Model.denote ops.decode)
    (fun c => CRTLocalProgram.Model.constant ops.zeroRun.1 c J)
    (CRTLocalProgram.Model.zero ops.zeroRun.1 J)
    (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J)
    (ops.decode theta) (Fixed.mul ops.program) (Fixed.add ops.program)
    (CRTLocalProgram.Model.zero_denote ops.decode _ ops.zero_correct J)
    (CRTLocalProgram.Model.linear_denote ops.decode _ _ _ ops.zero_correct ops.one_correct J)
    (fun c => CRTLocalProgram.Model.constant_denote ops.decode _ c ops.zero_correct J)
    (CRTLocalProgram.Model.mul_denote ops) (CRTLocalProgram.Model.add_denote ops) P

/-- Native multiply/add contracts are discharged here. The only remaining
premises describe the runtime scalar row, constants, caches, and scratch. -/
theorem native_shift_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i)=[])
    (h121 : s 121=[]) (h122 : s 122=[])
    (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
    (hJcount : (s 193).length=J)
    (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
    (P : List (Coeff (baseWidth p t) d)) (theta : Coeff (baseWidth p t) d)
    (hrow : s 219=HornerProgram.encodePolynomial RingProgram.flat P)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (he : ∀ i ∈ shiftScratch, s i=[]) :
    ExecutesIn (shift Fixed.mulCommand AddService.command)
      (shiftBudget P.length J (d*baseWidth p t)
        (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)) s
      (Function.update (Function.update s 219 []) 240
        (Fixed.encode (shiftedValue ops J theta P))) := by
  apply shift_run s RingProgram.flat Fixed.encode
    (fun c => CRTLocalProgram.Model.constant ops.zeroRun.1 c J)
    Fixed.mulCommand AddService.command (Fixed.mul ops) (Fixed.add ops)
    (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)
    J (d*baseWidth p t)
  · exact Fixed.mul_spec p t M cache ops table hB hz hadd hmul s J scalarWidth frame
      H hempty h121 h122 hcache hJcount
  · exact Fixed.add_spec p t M cache ops table hB hadd s J scalarWidth frame H
  · exact RingProgram.flat_length
  · exact Fixed.encode_length
  · intro c
    simpa [PerturbationProgram.Padding.cell,hzero,CRTLocalProgram.Model.constant] using
      (CRTLocalProgram.Model.padded_encode ops.zeroRun.1 c ops.zeroRun.1 hzero J).symm
  all_goals assumption

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
