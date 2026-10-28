import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramModel

namespace OAI.Algorithms

/-! Correctness of one fixed native bit program for exact count recovery from
physically stored Hasse jets over the actual searched ring model. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

theorem program_correct (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t)) :
    ∃ (b : Coeff t d) (rf : Fin 16 → Bool),
      RunsIn program (budget Q J t d (input.stacks 194).length (input.stacks 202).length + 1)
        (input.withPC (some program.entry))
        ((⟨rf, Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode b = (count : a.O t) ∧
      a.decodeCount t ht ((RingProgram.modelRing t ht hd a M cache).decode b) = count := by
  let ops := RingProgram.modelRing t ht hd a M cache
  let theta := fun i => ops.decode (nodes i)
  let inverse := LocalValue.inverse theta (3^d) t J
  obtain ⟨steps, hsteps, out, b, he, hout, hvalue⟩ := command_value t ht hd a M cache hcanon hzbits
    J hJpos hB nodes jets minusOne hminus input hscalar scalarWidth frame hpoly hclean
    hzero hone hneg hJ hnodes hjets hexponent hprecision
  have hi : ∀ i, inverse i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1 := by
    intro i
    exact LocalValue.inverse_correct (a.rho t ht) theta (3^d)
      (by simpa only [Nat.card_eq_fintype_card] using a.residue_cardinality)
      (3 : a.O t) t (a.prime_power_zero t)
      (fun x hx => (a.rho_eq_zero_iff t ht x).mp hx) hdistinct J hJpos i
  have hv : ops.decode b = (count : a.O t) := by
    rw [hvalue, scalar_value_eq_target a t ht theta J hJpos hdistinct inverse
      (fun i => CRTLocalProgram.Model.denote ops.decode (jets i)) hi target hdegree htargetJets,
      htarget]
  have heq : out = (⟨out.regs, Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b)⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hout
  rw [heq] at he
  refine ⟨b, out.regs, ?_, hv, ?_⟩
  · exact ⟨steps+1, Nat.add_le_add_right hsteps 1, compiled_halt_trace he 256 261⟩
  · exact scalar_decode_count a t ht hd.ne' (ops.decode b) count m n hcount hlarge hv

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
