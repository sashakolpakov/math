import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeFrame

namespace OAI.Algorithms

/-! The closed reconstruction tail, parameterized only by physical readiness
and mathematical facts about the stored nodes and jets. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

attribute [local irreducible] Count.Prepare.ports

noncomputable section

def countInput (a : Data) := Count.project (Count.Prepare.output a)
def countTail : Code := .seq Count.Prepare.command (.seq Count.command Residual.finish)
def finalStacks (input : Data) (word : List Bool) : Fin 768 → List Bool :=
  Function.update (Function.update (Function.update
    (Function.update (Count.Prepare.output input).stacks 323 word) 265 []) 702 []) 703 []

/-- A certificate about the actual input tapes. No execution field or
arithmetic callback occurs in this interface. -/
structure Recovery (input : Data) where
  t : ℕ
  d : ℕ
  Q : ℕ
  J : ℕ
  ht : 0 < t
  hd : 0 < d
  hQ : 0 < Q
  hJ : 0 < J
  hB : 0 < baseWidth 3 t
  model : RingModel.Data d
  modulus : SubexpPreparedQuartic.Modulus 3 t
  cache : RingProgram.ScalarCache 3 t
  canonicalZero : BinaryArithmetic.toNat cache.zero.val  <  3^t
  zeroBits : cache.zero.val=List.replicate (baseWidth 3 t) false
  nodes : Fin Q → ReconstructionProgram.Native.Coeff t d
  jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J
  minusOne : ReconstructionProgram.Native.Coeff t d
  negativeOne : (RingProgram.modelRing t ht hd model modulus cache).decode minusOne = -1
  scalarReady : HornerProgram.Services.NativeReady 3 t modulus cache
    (HornerProgram.modelTable t model modulus cache)
    (ReconstructionProgram.NativeState.arithmeticBase (countInput input))
  scalarWidth : List Bool
  polyFrame : Fin 6 → List Bool
  polynomialReady : PairSpec.BaseReady 3 t modulus cache
    (HornerProgram.modelTable t model modulus cache)
    (ReconstructionProgram.NativeState.arithmeticBase (countInput input)) scalarWidth polyFrame
  zero : (countInput input).stacks 280=RingProgram.flat (RingProgram.modelProgram t model modulus cache).zeroRun.1
  one : (countInput input).stacks 207=RingProgram.flat (RingProgram.modelProgram t model modulus cache).oneRun.1
  negative : (countInput input).stacks 211=RingProgram.flat minusOne
  order : (countInput input).stacks 243=List.replicate J true
  nodeWords : (countInput input).stacks 256=(List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i))
  jetWords : (countInput input).stacks 265=(List.finRange Q).flatMap (fun i => Fixed.encode (jets i))
  exponent : ((countInput input).stacks 209).length=3^d-2
  precision : ((countInput input).stacks 212).length=t
  distinct : Function.Injective (fun i => model.rho t ht
    ((RingProgram.modelRing t ht hd model modulus cache).decode (nodes i)))
  target : Polynomial (model.O t)
  degree : target.natDegree < Q*J
  hasJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd model modulus cache)
    nodes J (fun i => (jets i).1) target
  count : ℕ
  m : ℕ
  n : ℕ
  countBound : count ≤ m*2^n
  large : m*2^n < 3^t
  constant : target.eval 0=(count : model.O t)
  modulusValue : BinaryArithmetic.toNat ((countInput input).stacks 194)=3^t
  width : ((countInput input).stacks 202).length=baseWidth 3 t

def Recovery.cost {input : Data} (r : Recovery input) : ℕ :=
  Count.recoveryBudget r.Q r.J r.t r.d
    ((countInput input).stacks 194) ((countInput input).stacks 202)

def tailBudget (input : Data) (r : Recovery input) : ℕ :=
  Count.Prepare.budget input+r.cost+
    2*(input.stacks 265).length+2*(input.stacks 702).length+2*(input.stacks 703).length+9

theorem finish_cost_from_count (input out : Data)
    (hs : out.stacks=Function.update (Count.Prepare.output input).stacks 323 (out.stacks 323)) :
    Residual.finishCost out=
      2*(input.stacks 265).length+2*(input.stacks 702).length+2*(input.stacks 703).length+9 := by
  have h265 := Count.Prepare.output_input input 265 (by simp)
  have h702 := Count.Prepare.output_high_frame input 702 (by decide) (by decide)
  have h703 := Count.Prepare.output_high_frame input 703 (by decide) (by decide)
  have o265 : out.stacks 265=input.stacks 265 :=
    (show out.stacks 265=(Count.Prepare.output input).stacks 265 from by simpa only [Function.update_of_ne (by decide : (265 : Fin 768)≠323)] using congrFun hs 265).trans h265
  have o702 : out.stacks 702=input.stacks 702 :=
    (show out.stacks 702=(Count.Prepare.output input).stacks 702 from by simpa only [Function.update_of_ne (by decide : (702 : Fin 768)≠323)] using congrFun hs 702).trans h702
  have o703 : out.stacks 703=input.stacks 703 :=
    (show out.stacks 703=(Count.Prepare.output input).stacks 703 from by simpa only [Function.update_of_ne (by decide : (703 : Fin 768)≠323)] using congrFun hs 703).trans h703
  simp only [Residual.finishCost,o265,o702,o703]

theorem recover (input : Data) (r : Recovery input) :
    ∃ time out, time ≤ tailBudget input r ∧ Eval countTail time input out ∧
      BinaryArithmetic.toNat (out.stacks 323)=r.count ∧
      (out.stacks 323).length=((countInput input).stacks 194).length+baseWidth 3 r.t ∧
      out.stacks 324=[] ∧
      (∀ i,Query.Protected i → i≠323 → out.stacks i=input.stacks i) ∧
      LeafNodeSamplesProgram.RegFrame input.regs out.regs ∧
      out.stacks=finalStacks input (out.stacks 323) := by
  let : NeZero r.Q := ⟨Nat.ne_of_gt r.hQ⟩
  have hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts,
      (countInput input).stacks j = [] := by
    intro j hj
    change (Count.Prepare.output input).stacks (Count.crtStacks j) = []
    exact Count.Prepare.output_clean input j hj
  obtain ⟨k,out,hk,he,hvalue,hlen,h324,h5,h10,hs,hr⟩ :=
    Count.command_correct r.t r.ht r.hd r.model r.modulus r.cache r.canonicalZero r.zeroBits
      r.J r.hJ r.hB r.nodes r.jets r.minusOne r.negativeOne (countInput input)
      r.scalarReady r.scalarWidth r.polyFrame r.polynomialReady
      hclean r.zero r.one r.negative r.order r.nodeWords r.jetWords
      r.exponent r.precision r.distinct r.target r.degree r.hasJets
      r.count r.m r.n r.countBound r.large r.constant (Count.Prepare.output input)
      r.modulusValue r.width (Count.Prepare.output_reader input)
  have hi : Count.install (Count.Prepare.output input) (countInput input)=Count.Prepare.output input :=
    Count.install_project _
  rw [hi] at he hs hr
  refine ⟨Count.Prepare.budget input+(k+Residual.finishCost out),Residual.finished out,?_,
    (Count.Prepare.command_eval input).seq (he.seq (Residual.finish_eval out)),?_,?_,?_,?_,?_,?_⟩
  · rw [finish_cost_from_count input out hs]
    unfold tailBudget Recovery.cost at *
    omega
  · simpa only [Residual.finished_frame out 323 (by decide) (by decide) (by decide)] using hvalue
  · simpa only [Residual.finished_frame out 323 (by decide) (by decide) (by decide)] using hlen
  · simpa only [Residual.finished_frame out 324 (by decide) (by decide) (by decide)] using h324
  · intro i hp ho
    rw [finished_protected out i hp,hs,Function.update_of_ne ho]
    exact prepare_protected input i hp ho
  · intro i hlo hhi
    exact (finished_register out i (by omega)).trans
      ((hr i hlo).trans (Count.Prepare.output_register_frame input i (by omega)))
  · rw [Residual.finished_frame out 323 (by decide) (by decide) (by decide),
      Residual.finished_stacks]
    exact congrArg (fun st : Fin 768 → List Bool => Function.update (Function.update (Function.update st 265 []) 702 []) 703 []) hs

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
