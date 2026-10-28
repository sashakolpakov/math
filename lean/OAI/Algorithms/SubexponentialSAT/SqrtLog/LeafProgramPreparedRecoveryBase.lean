import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramConstantsModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgramModel

namespace OAI.Algorithms

/-! Physical reconstruction readiness from the actual ring producer and its
preserved small cache bank. The sampled node and jet streams remain explicit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing LeafParametersProgram
open Residual.Native
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section

private theorem countOutputInput_256 :
    (256 : Fin 768) ∈ ([194,201,202,203,204,207,209,211,212,243,256,265,280] :
      List (Fin 768)) := by
  simp

private theorem countOutputInput_265 :
    (265 : Fin 768) ∈ ([194,201,202,203,204,207,209,211,212,243,256,265,280] :
      List (Fin 768)) := by
  simp

 def ringPorts : List (Fin 320) := [194,201,202,203,204,207,209,211,212,243,280]
 def RingFrame (e : LeafRingSetupProgram.Data) (input : Factor.Data) : Prop :=
  ∀ i∈ringPorts,input.stacks (Count.crtStacks i)=e.stacks (i.castAdd 320)

 theorem count_ringFrame {e : LeafRingSetupProgram.Data} {input : Factor.Data}
    (hf : RingFrame e input) (i : Fin 320) (hi : i∈ringPorts) :
    (countInput input).stacks i=e.stacks (i.castAdd 320) := by
  simp only [countInput, Count.project, projectState, Function.comp_apply]
  rw [Count.Prepare.output_frame]
  · exact hf i hi
  · apply Count.Prepare.protected_not_mem
    simp only [ringPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [Count.Prepare.protectedInputs, Count.crtStacks]
  · intro h
    have hv := congrArg Fin.val h
    change i.val=699 at hv
    omega

attribute [local irreducible] Count.Prepare.ports

 theorem count_clean (input : Factor.Data) :
    ∀ i∈ReconstructionProgram.InputReady.emptyPorts,(countInput input).stacks i=[] := by
  intro i hi
  exact Count.Prepare.output_arithmetic_clean input i hi

 def ofProduced (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (input : Factor.Data) (hf : RingFrame e input)
    (Q J : ℕ) (hQ : 0 < Q) (hJ : 0 < J) (hj : m.val 42=J)
    (hfield : Q < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2)
    (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 (m.val 33)) (m.val 34) J)
    (hnodes : input.stacks 256=(List.finRange Q).flatMap
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))))
    (hjets : input.stacks 265=(List.finRange Q).flatMap (fun i => DensePolynomialProgram.Fixed.encode (jets i)))
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (hdegree : target.natDegree < Q*J)
    (hhas : Reconstruction.HasJets (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin Q => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)) J
      (fun i => (jets i).1) target)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0=(count : (IrreducibleSearch.data hd).O (m.val 33))) :
    {r : Recovery input //
      r.t=m.val 33 ∧ r.d=m.val 34 ∧ r.Q=Q ∧ r.J=J ∧ r.count=count} := by
  have fw := count_ringFrame hf
  have hm := (fw 194 (by simp [ringPorts])).trans hp.caches.modulus
  have hw := congrArg List.length (fw 202 (by simp [ringPorts])) |>.trans hp.caches.width
  have hz := (fw 203 (by simp [ringPorts])).trans hp.caches.scalarZero
  have htable := (fw 201 (by simp [ringPorts])).trans hp.native.table
  have hdw := congrArg List.length (fw 204 (by simp [ringPorts])) |>.trans hp.caches.degree
  have hzero := (fw 280 (by simp [ringPorts])).trans hp.caches.fullZero_model
  have hlen := congrArg List.length (fw 280 (by simp [ringPorts])) |>.trans hp.native.fullZeroLength
  exact ⟨{
    t := m.val 33, d := m.val 34, Q := Q, J := J,
    ht := ht, hd := hd, hQ := hQ, hJ := hJ,
    hB := Nat.mul_pos ht (by omega),
    model := IrreducibleSearch.data hd, modulus := M, cache := cache,
    canonicalZero := hp.caches.canonical, zeroBits := hp.zero_bytes,
    nodes := fun i => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1),
    jets := jets, minusOne := Constants.constantCode (m.val 34) cache.minusOne cache.zero,
    negativeOne := Constants.minusOne_decode _ ht hd _ M cache,
    scalarReady := ReconstructionProgram.InputReady.nativeReady 3 _ M cache _ (countInput input)
      (count_clean input) hm hw hz htable hdw,
    scalarWidth := (countInput input).stacks 202,
    polyFrame := ReconstructionProgram.InputReady.lowFrame (countInput input),
    polynomialReady := ReconstructionProgram.InputReady.polynomialReady 3 _ M cache _ (countInput input)
      (count_clean input) hm hw hz htable hdw hlen,
    zero := hzero,
    one := (fw 207 (by simp [ringPorts])).trans hp.caches.fullOne_model,
    negative := (fw 211 (by simp [ringPorts])).trans
      (hp.caches.fullMinusOne.trans (Constants.constantCode_flat _ _ _).symm),
    order := (fw 243 (by simp [ringPorts])).trans (by simpa [hj] using hp.jetOrder),
    nodeWords := (Count.Prepare.output_input input 256 countOutputInput_256).trans hnodes,
    jetWords := (Count.Prepare.output_input input 265 countOutputInput_265).trans hjets,
    exponent := (congrArg List.length ((fw 209 (by simp [ringPorts])).trans hp.exponent)).trans
      (by simp only [List.length_replicate,hexponent]),
    precision := (congrArg List.length ((fw 212 (by simp [ringPorts])).trans hp.caches.precision)).trans
      (by simp only [List.length_replicate]),
    distinct := RingNodeProgram.generated_residue_injective _ ht hd _ M cache Q hfield,
    target := target, degree := hdegree, hasJets := hhas,
    count := count, m := multiplicity, n := ambient, countBound := hcount, large := hlarge, constant := hconstant,
    modulusValue := hm ▸ M.value, width := hw },rfl,rfl,rfl,rfl,rfl⟩

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery

end OAI.Algorithms
