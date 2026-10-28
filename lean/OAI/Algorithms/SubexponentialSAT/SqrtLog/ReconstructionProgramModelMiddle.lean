import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramIteration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramLocalValue
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramNative

namespace OAI.Algorithms

/-! The actual model-specific native Hermite iteration. Every arithmetic
service and every local correction trace is discharged here. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

abbrev Coeff (t d : ℕ) := DensePolynomialProgram.Coeff (baseWidth 3 t) d

noncomputable def term {d Q : ℕ} (t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (nodes : Fin Q → Coeff t d)
    (J : ℕ) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J) (i : Fin Q) : a.O t :=
  let ops := RingProgram.modelRing t ht hd a M cache
  let theta := fun j => ops.decode (nodes j)
  (JetCRT.cofactor theta J i).eval 0 *
    (TruncatedInverse.correction theta J (LocalValue.inverse theta (3^d) t J)
      (fun j => CRTLocalProgram.Model.denote ops.decode (jets j)) i).eval (-theta i)

theorem middle_run (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (_hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne acc : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (processed remaining : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (input.stacks ∘ localPorts))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (input.stacks ∘ localPorts) scalarWidth frame)
    (hbuffers : ∀ j, input.stacks (localPorts (SubexpConvolutionControl.bufferPorts j)) = [])
    (hclean : ∀ j ∈ Middle.cleanPorts, input.stacks j = [])
    (hlocalClean : ∀ j ∈ CRTLocalProgram.localWork, input.stacks (localPorts j) = [])
    (hzero : input.stacks 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hnode : input.stacks 213 = RingProgram.flat (nodes i))
    (hnodes : input.stacks 214 = (List.ofFn nodes).flatMap RingProgram.flat)
    (hindex : (input.stacks 216).length = i.val)
    (hjet : input.stacks 225 = Fixed.encode (jets i))
    (hJ : input.stacks 243 = List.replicate J true)
    (hr : input.stacks 257 = (remaining.map nodes).flatMap RingProgram.flat)
    (hp : input.stacks 258 = (processed.map nodes).flatMap RingProgram.flat)
    (hx : input.stacks 259 = RingProgram.flat (nodes i))
    (hacc : input.stacks 261 = RingProgram.flat acc)
    (h277 : input.stacks 277 = DensePolynomialProgram.encode
      (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t) :
    ∃ n ≤ Middle.budget Q J (d*baseWidth 3 t)
        (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
        (HornerProgram.Services.addBudget (baseWidth 3 t) d)
        (CRTLocalProgram.Native.budget Q i.val (3^d) t d J), ∃ rf b,
      Eval middle n input ⟨rf, Function.update input.stacks 261 (RingProgram.flat b)⟩ ∧
      (RingProgram.modelRing t ht hd a M cache).decode b =
        (RingProgram.modelRing t ht hd a M cache).decode acc + term t ht hd a M cache nodes J jets i := by
  let ops := RingProgram.modelRing t ht hd a M cache
  let s := input.stacks ∘ localPorts
  let prepared := (Local.prepared input).stacks ∘ localPorts
  have hprep : prepared = Function.update (Function.update s 192 (input.stacks 277))
      193 (input.stacks 243) := by
    funext j
    have hj : localPorts j = (192 : Fin 320) ↔ j = 192 := by
      constructor
      · intro h; apply Fin.ext; exact congrArg (fun k : Fin 320 => k.val) h
      · rintro rfl; rfl
    have hj' : localPorts j = (193 : Fin 320) ↔ j = 193 := by
      constructor
      · intro h; apply Fin.ext; exact congrArg (fun k : Fin 320 => k.val) h
      · rintro rfl; rfl
    simp [prepared, s, Local.prepared, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks,
      Function.comp_def, Function.update_apply, hj, hj',
      hclean 192 (by simp [Middle.cleanPorts]), hclean 193 (by simp [Middle.cleanPorts])]
  have hscalar' : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) prepared := by
    rw [hprep]
    exact hscalar.update_polynomial_caches _ _
  have hpoly' : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      prepared scalarWidth frame := by
    rw [hprep]
    exact PairSpec.BaseReady.update_cache 3 t M cache (HornerProgram.modelTable t a M cache)
      (PairSpec.BaseReady.update_cache 3 t M cache (HornerProgram.modelTable t a M cache)
        hpoly 192 (Or.inl rfl) _) 193 (Or.inr rfl) _
  have hlocal : ∀ j ∈ CRTLocalProgram.localWork, prepared j = [] := by
    intro j hj
    have h192 : j ≠ (192 : Fin 256) := by intro he; subst j; simp [CRTLocalProgram.localWork] at hj
    have h193 : j ≠ (193 : Fin 256) := by intro he; subst j; simp [CRTLocalProgram.localWork] at hj
    simpa [hprep, s, localPorts, h192, h193] using hlocalClean j hj
  have hb : ∀ j, prepared (SubexpConvolutionControl.bufferPorts j) = [] := by
    intro j
    have h192 : SubexpConvolutionControl.bufferPorts j ≠ (192 : Fin 256) := by fin_cases j <;> decide
    have h193 : SubexpConvolutionControl.bufferPorts j ≠ (193 : Fin 256) := by fin_cases j <;> decide
    simpa [hprep, s, localPorts, h192, h193] using hbuffers j
  obtain ⟨c, rest, hhead, hrun⟩ := CRTLocalProgram.Native.command_run t ht hd a M cache hcanon
    prepared J (3^d) hJpos hB hscalar' scalarWidth frame hpoly' hb minusOne (nodes i)
    (List.ofFn nodes) (jets i)
    (by simpa [hprep, s, localPorts] using hzero)
    (by simpa [hprep, s, localPorts] using hone)
    (by simpa [hprep, s, localPorts] using hneg)
    (by simpa [hprep, s, localPorts] using hnode)
    (by simpa [hprep, s, localPorts] using hnodes)
    (by simpa [hprep, s, localPorts] using hjet)
    (by simpa [hprep, s, localPorts] using hJ)
    (by simp [hprep, hJ]) (by simp [hprep, h277])
    (by simpa [hprep, s, localPorts] using hexponent)
    (by simpa [hprep, s, localPorts] using hprecision) hlocal
  have hidx : (prepared 216).length = i.val := by simpa [hprep, s, localPorts] using hindex
  simp only [List.length_ofFn, hidx] at hrun hhead
  change (LocalValue.factorCode ops minusOne nodes J i).1 = c :: rest at hhead
  let correction := CRTLocalProgram.Model.corrected ops minusOne c (3^d) t
    (LocalValue.factorCode ops minusOne nodes J i) (jets i)
  change SubexpConvolutionControl.ExecutesIn localCode
      (CRTLocalProgram.Native.budget Q i.val (3^d) t d J) prepared
      (Function.update prepared 244 (List.map RingProgram.flat
        (CRTLocalProgram.Model.corrected ops minusOne c (3^d) t
          (LocalValue.factorCode ops minusOne nodes J i) (jets i)).1).flatten) at hrun
  have hrun' : SubexpConvolutionControl.ExecutesIn localCode
      (CRTLocalProgram.Native.budget Q i.val (3^d) t d J) prepared
      (Function.update prepared 244 (HornerProgram.encodePolynomial RingProgram.flat correction.1)) := by
    dsimp only [correction]
    simpa only [localCode, CRTLocalProgram.Native.command, Fixed.encode,
      DensePolynomialProgram.encode, HornerProgram.encodePolynomial,
      List.flatMap_def] using hrun
  have hdenote := LocalValue.corrected_denote ops minusOne hminus nodes (3^d) t J jets i c rest hhead
  have hscalarMul := HornerProgram.Services.multiply_spec 3 t M cache hcanon
    (HornerProgram.modelTable t a M cache) s hscalar
  have hscalarAdd := HornerProgram.Services.add_spec 3 t M cache
    (HornerProgram.modelTable t a M cache) s hscalar
  apply Middle.iteration_run RingProgram.flat ops.decode localCode HornerProgram.Services.multiply
    HornerProgram.Services.add (CRTLocalProgram.Model.scalarMul ops) (CRTLocalProgram.Model.scalarAdd ops)
    _ _ _ _ J input nodes remaining processed i hfull ops.oneRun.1 minusOne ops.zeroRun.1 acc
    hscalarMul hscalarAdd ops.mul_correct ops.add_correct ops.one_correct hminus ops.zero_correct
    RingProgram.flat_length (Nat.mul_pos hd hB) hr hp hone hneg hzero hx hacc hJ
    (by simp [h277, DensePolynomialProgram.encode, RingProgram.flat_length]) hclean
    correction.1 correction.2 _ hdenote hrun'

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
