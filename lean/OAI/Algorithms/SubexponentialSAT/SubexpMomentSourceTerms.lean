import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceTraversal

namespace OAI.Algorithms

/-! Typed unweighted template entries and their actual weighted-term assembly. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

structure ContextGood (ctx : Context) (a : Fin ctx.dimension → ℕ) : Prop where
  exponent : ctx.exponent = SymbolicCost.unaryWords (List.ofFn a)
  indexWidth : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension
  padding : ctx.width.length ≤ ctx.target.length
  unitLength : ctx.unit.length = ctx.target.length
  unitValue : (BinaryArithmetic.toNat ctx.unit : ZMod (BinaryArithmetic.toNat ctx.modulus)) = 1
  modulusLength : ctx.modulus.length ≤ ctx.target.length+1
  positive : 0 < BinaryArithmetic.toNat ctx.modulus
  capacity : BinaryArithmetic.toNat ctx.modulus ≤ 2^ctx.target.length

structure PointData (ctx : Context) where
  coordinates : Fin ctx.dimension → Word
  support : List (Fin ctx.dimension)
  nodup : support.Nodup
  width : ∀ i, (coordinates i).length = ctx.width.length

def PointData.descriptor {ctx : Context} (p : PointData ctx) : Descriptor :=
  pointDescriptor p.coordinates p.support

structure TermData (ctx : Context) where
  point : PointData ctx
  factors : List (List SubexpTableSource.Row)

def TermData.template {ctx : Context} (t : TermData ctx) : Term :=
  ⟨t.point.descriptor,t.factors⟩

structure WeightResult (ctx : Context) (a : Fin ctx.dimension → ℕ) (p : PointData ctx) where
  output : Word
  records : List SubexpWeightControl.WeightRecord
  good : List.Forall₂ (SubexpWeightGather.GoodRecord a p.coordinates ctx.target)
    p.support.reverse records
  length : output.length = ctx.target.length
  value : (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat ctx.modulus)) =
    Separation.coordinateWeight p.support.toFinset id a
      (fun i => (BinaryArithmetic.toNat (p.coordinates i) : ZMod (BinaryArithmetic.toNat ctx.modulus)))

def WeightResult.literal {ctx : Context} {a : Fin ctx.dimension → ℕ} {p : PointData ctx}
    (w : WeightResult ctx a p) : Word :=
  SubexpScalarLiteralProgram.rawLiteral ctx.dimension
    (SubexpQuarticMarshal.marshalBits w.output ctx.target)

structure TermResult (ctx : Context) (a : Fin ctx.dimension → ℕ) where
  input : TermData ctx
  weight : WeightResult ctx a input.point

def TermResult.prepared {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (t : TermResult ctx a) : SubexpBlockAssembly.Term :=
  ⟨t.weight.literal,t.input.factors⟩

def termBudget (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (t : TermData ctx) (out : TermResult ctx a) : ℕ :=
  captureBudget ctx a t.point.coordinates t.point.support out.weight.records+
    40*SubexpSymbolicCost.indexBits ctx.dimension+160*ctx.target.length+82+
    12*(Encoding.encodeList SubexpTableSource.encodeRows t.factors).length+12+
    13*(SubexpBlockAssembly.encodeTerm out.prepared).length+16

theorem packComplete_measured (i j : Fin 7) (v p c : Bool) (input zero one : Word)
    (buffers : SubexpBlockAssembly.Buffers) :
    Eval (SubexpBlockAssembly.packComplete (SubexpBlockAssembly.bufferPort i)
      (SubexpBlockAssembly.bufferPort j)) (13*(buffers i).length+15)
      (SubexpBlockAssembly.state v p c input zero one buffers)
      (SubexpBlockAssembly.state false false true input zero one
        (SubexpBlockAssembly.packUpdate i j buffers)) := by
  have h1 := SubexpBlockAssembly.transferBuffer_measured i v p c input zero one buffers
  have h2 := SubexpBlockAssembly.appendRecord_measured j false false c input zero one
    (buffers i).reverse (Function.update buffers i [])
  have h3 := SubexpBlockAssembly.clearPayload_measured false false true input zero one
    (buffers i).reverse (SubexpBlockAssembly.emit j
      (SubexpBlockAssembly.record (buffers i).reverse) (Function.update buffers i []))
  simp only [List.length_reverse] at h2 h3
  have h := Eval.seq h1 (Eval.seq h2 h3)
  have hcost : 3 * (buffers i).length + 3 +
      (8 * (buffers i).length + 9 + (2 * (buffers i).length + 3)) =
      13 * (buffers i).length + 15 := by
    omega
  rw [hcost] at h
  exact h

/-- The term body computes its weight from the current exponent, copies only
the factor data from its reusable template, and frames the complete term. -/
theorem termBody_eval (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (hc : ContextGood ctx a) (t : TermData ctx) (r : Fin 8 → Bool)
    (rest captured : Word) (buffers : SubexpBlockAssembly.Buffers) (h2 : buffers 2 = []) :
    ∃ (out : TermResult ctx a) (n : ℕ) (rf : Fin 8 → Bool), out.input = t ∧ n ≤ termBudget ctx a t out ∧
      Eval termBody n
        (state ctx r (encodeTerm t.template ++ rest) buffers [] [] [] captured)
        (state ctx rf rest (SubexpBlockAssembly.emit 3
          (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeTerm out.prepared)) buffers)
          [] [] [] captured) := by
  let factorBytes := Encoding.encodeList SubexpTableSource.encodeRows t.factors
  obtain ⟨nw,rWeight,output,records,hnw,hgood,hw,hlen,hvalue⟩ := weightFrame_eval ctx r a
    t.point.coordinates t.point.support (Encoding.frame factorBytes ++ rest) captured buffers 2
    hc.exponent hc.indexWidth t.point.nodup t.point.width hc.padding hc.unitLength
    hc.unitValue hc.modulusLength hc.positive hc.capacity
  let weight : WeightResult ctx a t.point := ⟨output,records,hgood,hlen,hvalue⟩
  let out : TermResult ctx a := ⟨t,weight⟩
  let afterWeight := SubexpBlockAssembly.emit 2 (Encoding.frame weight.literal) buffers
  let r1 := flags rWeight false false (rWeight 2)
  let r2 := flags r1 false false (r1 2)
  have hf := base_eval ctx rWeight (Encoding.frame factorBytes ++ rest) rest
    afterWeight afterWeight [] factorBytes [] [] captured false false (rWeight 2)
    (SubexpBlockAssembly.capture_measured (rWeight 0) (rWeight 1) (rWeight 2) factorBytes
      rest ctx.zero ctx.one afterWeight)
  have ht := base_eval ctx r1 rest rest afterWeight
    (SubexpBlockAssembly.emit 2 factorBytes afterWeight) factorBytes [] [] [] captured
    false false (r1 2)
    (SubexpBlockAssembly.transferPayload_measured 2 (r1 0) (r1 1) (r1 2)
      rest ctx.zero ctx.one factorBytes afterWeight)
  let termBuffers := SubexpBlockAssembly.emit 2 (SubexpBlockAssembly.encodeTerm out.prepared) buffers
  have hb : SubexpBlockAssembly.emit 2 factorBytes afterWeight = termBuffers := by
    exact SubexpBlockAssembly.emit_emit 2 (Encoding.frame weight.literal) factorBytes buffers
  rw [hb] at ht
  have hp := base_eval ctx r2 rest rest termBuffers
    (SubexpBlockAssembly.packUpdate 2 3 termBuffers) [] [] [] [] captured false false true
    (packComplete_measured 2 3 (r2 0) (r2 1) (r2 2) rest ctx.zero ctx.one termBuffers)
  have hpResult : SubexpBlockAssembly.packUpdate 2 3 termBuffers =
      SubexpBlockAssembly.emit 3
        (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeTerm out.prepared)) buffers :=
    SubexpBlockAssembly.packUpdate_emitted 2 3 buffers (SubexpBlockAssembly.encodeTerm out.prepared) h2
  rw [hpResult] at hp
  have h := Eval.seq hw (Eval.seq (Eval.seq hf ht) hp)
  norm_num [SubexpBlockAssembly.bufferPort] at h
  refine ⟨out,nw+((9*factorBytes.length+7+1+(3*factorBytes.length+3+1))+
    (13*(termBuffers 2).length+15+1)),flags r2 false false true,rfl,?_,?_⟩
  · have hlength : (termBuffers 2).length = (SubexpBlockAssembly.encodeTerm out.prepared).length := by
      simp [termBuffers,SubexpBlockAssembly.emit,h2]
    change nw+((9*factorBytes.length+7+1+(3*factorBytes.length+3+1))+
      (13*(termBuffers 2).length+15+1)) ≤
      captureBudget ctx a t.point.coordinates t.point.support records+
        40*SubexpSymbolicCost.indexBits ctx.dimension+160*ctx.target.length+82+
        12*factorBytes.length+12+13*(SubexpBlockAssembly.encodeTerm out.prepared).length+16
    rw [hlength]
    omega
  · simpa only [termBody,copyFactors,packInto,TermData.template,PointData.descriptor,
      encodeTerm,factorBytes,List.append_assoc] using h

theorem encodeList_map {α β : Type*} (f : β → Word) (g : α → β) (xs : List α) :
    Encoding.encodeList f (xs.map g) = Encoding.encodeList (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,Encoding.encodeList,ih]

def groupBudget (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (ts : List (TermData ctx)) (outs : List (TermResult ctx a)) : ℕ :=
  scanSteps (fun t => encodeTerm t.template) (termBudget ctx a) ts outs +
    13*(SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared)).length+21

section GroupExecution

attribute [local irreducible] WeightResult.literal TermResult.prepared

theorem groupBody_eval (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (hc : ContextGood ctx a) (ts : List (TermData ctx)) (r : Fin 8 → Bool)
    (rest captured : Word) (buffers : SubexpBlockAssembly.Buffers)
    (h2 : buffers 2 = []) (h3 : buffers 3 = []) :
    ∃ (outs : List (TermResult ctx a)) (n : ℕ) (rf : Fin 8 → Bool),
      List.Forall₂ (fun t out => out.input = t) ts outs ∧ n ≤ groupBudget ctx a ts outs ∧
      Eval groupBody n
        (state ctx r (encodeGroup (ts.map TermData.template) ++ rest) buffers [] [] [] captured)
        (state ctx rf rest (SubexpBlockAssembly.emit 6
          (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared)))
          buffers) [] [] [] captured) := by
  let update := fun (out : TermResult ctx a) (b : SubexpBlockAssembly.Buffers) =>
    SubexpBlockAssembly.emit 3
      (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeTerm out.prepared)) b
  obtain ⟨outs,ns,rs,hrelation,hns,hs⟩ := scan_relational ctx termBody
    (fun t => encodeTerm (TermData.template t)) (termBudget ctx a)
    (fun t out => out.input = t) update (fun b => b 2 = [])
    (fun t r rest captured b hb => termBody_eval ctx a hc t r rest captured b hb)
    (by intro t out b h hb; simpa [update,SubexpBlockAssembly.emit] using hb)
    ts r rest captured buffers h2
  let records := (outs.map (fun out =>
    SubexpBlockAssembly.record (SubexpBlockAssembly.encodeTerm out.prepared))).flatten
  let groupBuffers := SubexpBlockAssembly.emit 3 records buffers
  have hfold : outs.foldl (fun b out => update out b) buffers = groupBuffers :=
    SubexpBlockAssembly.fold_emit 3
      (fun out => SubexpBlockAssembly.record (SubexpBlockAssembly.encodeTerm out.prepared)) outs buffers
  rw [hfold] at hs
  have hcloseLocal := SubexpBlockAssembly.closeInto_measured 3 6 (rs 0) (rs 1) (rs 2)
    rest ctx.zero ctx.one groupBuffers
  change Eval (SubexpBlockAssembly.closeInto 16 21) _ _ _ at hcloseLocal
  have hc := base_eval ctx rs rest rest groupBuffers
    (SubexpBlockAssembly.closeUpdate 3 6 groupBuffers) [] [] [] [] captured false false true
    hcloseLocal
  have hbytes : records ++ [false] =
      SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared) := by
    rw [SubexpBlockAssembly.encodeGroup,SubexpBlockAssembly.encodeList_eq_records]
    simp only [records,List.map_map,Function.comp_def]
  have hclose : SubexpBlockAssembly.closeUpdate 3 6 groupBuffers =
      SubexpBlockAssembly.emit 6
        (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared)))
        buffers := by
    rw [SubexpBlockAssembly.close_emitted 3 6 records buffers h3,hbytes]
  rw [hclose] at hc
  have h := Eval.seq hs hc
  refine ⟨outs,ns+(13*(groupBuffers 3).length+30+1),
    flags rs false false true,hrelation,?_,?_⟩
  · have hlen : (groupBuffers 3).length + 1 =
        (SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared)).length := by
      rw [←hbytes]
      simp [groupBuffers,SubexpBlockAssembly.emit,h3]
    unfold groupBudget
    omega
  · simpa only [groupBody,encodeGroup,encodeList_map] using h

end GroupExecution

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
