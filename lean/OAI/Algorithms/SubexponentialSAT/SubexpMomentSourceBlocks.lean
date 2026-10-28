import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceTerms

namespace OAI.Algorithms

/-! Serial group and block packing from the current-exponent weight calls. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

structure BlockData (ctx : Context) where
  point : PointData ctx
  groups : List (List (TermData ctx))

def BlockData.template {ctx : Context} (b : BlockData ctx) : Block :=
  ⟨b.point.descriptor,b.groups.map (List.map TermData.template)⟩

structure BlockResult (ctx : Context) (a : Fin ctx.dimension → ℕ) where
  input : BlockData ctx
  weight : WeightResult ctx a input.point
  groups : List (List (TermResult ctx a))
  agreement : List.Forall₂ (List.Forall₂ (fun t out => out.input = t)) input.groups groups

def BlockResult.prepared {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (b : BlockResult ctx a) : SubexpBlockAssembly.Block :=
  ⟨b.weight.literal,b.groups.map (List.map TermResult.prepared)⟩

def blockGroupBytes {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (groups : List (List (TermResult ctx a))) : Word :=
  Encoding.encodeList SubexpBlockAssembly.encodeGroup (groups.map (List.map TermResult.prepared))

def blockBudget (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (b : BlockData ctx) (out : BlockResult ctx a) : ℕ :=
  captureBudget ctx a b.point.coordinates b.point.support out.weight.records+
    40*SubexpSymbolicCost.indexBits ctx.dimension+160*ctx.target.length+110+
    scanSteps (fun ts => encodeGroup (ts.map TermData.template)) (groupBudget ctx a) b.groups out.groups+
    6*(blockGroupBytes out.groups).length+13*(SubexpBlockAssembly.encodeBlock out.prepared).length

theorem closeBare_measured (i j : Fin 7) (v p c : Bool) (input zero one : Word)
    (buffers : SubexpBlockAssembly.Buffers) :
    Eval (SubexpBlockAssembly.closeBare (SubexpBlockAssembly.bufferPort i)
      (SubexpBlockAssembly.bufferPort j)) (6*(buffers i).length+14)
      (SubexpBlockAssembly.state v p c input zero one buffers)
      (SubexpBlockAssembly.state false false c input zero one
        (SubexpBlockAssembly.bareUpdate i j buffers)) := by
  let b := Function.update buffers i (false :: buffers i)
  have h1 := SubexpBlockAssembly.pushBuffer_measured i false v p c input zero one buffers
  have h2 := SubexpBlockAssembly.transferBuffer_measured i false p c input zero one b
  have h3 := SubexpBlockAssembly.transferPayload_measured j false false c input zero one
    (b i).reverse (Function.update b i [])
  have h := SubexpBlockAssembly.measured_result (Eval.seq h1 (Eval.seq h2 h3))
    (SubexpBlockAssembly.closeBare_work i j v p c input zero one buffers)
  have hcost : 2+(3*(b i).length+3+(3*(b i).reverse.length+3)) = 6*(buffers i).length+14 := by
    simp only [b,Function.update_same,List.length_cons,List.length_reverse]
    omega
  simpa only [hcost,SubexpBlockAssembly.closeBare] using h

section BlockExecution

attribute [local irreducible] WeightResult.literal TermResult.prepared

/-- The group scan is a sum of per-color inner traversals. It never constructs
the Cartesian product of the color coordinates. -/
theorem blockBody_eval (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (hc : ContextGood ctx a) (b : BlockData ctx) (r : Fin 8 → Bool)
    (rest captured : Word) (buffers : SubexpBlockAssembly.Buffers)
    (h2 : buffers 2 = []) (h3 : buffers 3 = []) (h4 : buffers 4 = []) (h6 : buffers 6 = []) :
    ∃ (out : BlockResult ctx a) (n : ℕ) (rf : Fin 8 → Bool), out.input = b ∧ n ≤ blockBudget ctx a b out ∧
      Eval blockBody n
        (state ctx r (encodeBlock b.template ++ rest) buffers [] [] [] captured)
        (state ctx rf rest (SubexpBlockAssembly.emit 5
          (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeBlock out.prepared)) buffers)
          [] [] [] captured) := by
  let groupInput := Encoding.encodeList encodeGroup (b.groups.map (List.map TermData.template))
  obtain ⟨nw,rWeight,output,records,hnw,hgood,hw,hlen,hvalue⟩ := weightFrame_eval ctx r a
    b.point.coordinates b.point.support (groupInput ++ rest) captured buffers 4
    hc.exponent hc.indexWidth b.point.nodup b.point.width hc.padding hc.unitLength
    hc.unitValue hc.modulusLength hc.positive hc.capacity
  let weight : WeightResult ctx a b.point := ⟨output,records,hgood,hlen,hvalue⟩
  have hweightLiteral : weight.literal = SubexpScalarLiteralProgram.rawLiteral ctx.dimension
      (SubexpQuarticMarshal.marshalBits output ctx.target) := by
    unfold WeightResult.literal
    rfl
  rw [←hweightLiteral] at hw
  let afterWeight := SubexpBlockAssembly.emit 4 (Encoding.frame weight.literal) buffers
  let update := fun (outs : List (TermResult ctx a)) (acc : SubexpBlockAssembly.Buffers) =>
    SubexpBlockAssembly.emit 6 (SubexpBlockAssembly.record
      (SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared))) acc
  obtain ⟨groups,ng,rg,hgroups,hng,hg⟩ := scan_relational ctx groupBody
    (fun ts => encodeGroup (ts.map TermData.template)) (groupBudget ctx a)
    (List.Forall₂ (fun t out => out.input = t)) update (fun acc => acc 2 = [] ∧ acc 3 = [])
    (fun ts r rest captured acc hacc => groupBody_eval ctx a hc ts r rest captured acc hacc.1 hacc.2)
    (by
      intro ts outs acc houts hacc
      simpa [update,SubexpBlockAssembly.emit] using hacc)
    b.groups rWeight rest captured afterWeight
    (by simpa [afterWeight,SubexpBlockAssembly.emit] using And.intro h2 h3)
  let out : BlockResult ctx a := ⟨b,weight,groups,hgroups⟩
  let groupRecords := (groups.map (fun outs => SubexpBlockAssembly.record
    (SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared)))).flatten
  let groupBuffers := SubexpBlockAssembly.emit 6 groupRecords afterWeight
  have hfold : groups.foldl (fun acc outs => update outs acc) afterWeight = groupBuffers :=
    SubexpBlockAssembly.fold_emit 6 (fun outs => SubexpBlockAssembly.record
      (SubexpBlockAssembly.encodeGroup (outs.map TermResult.prepared))) groups afterWeight
  rw [hfold] at hg
  have hgroupBytes : groupRecords ++ [false] = blockGroupBytes groups := by
    rw [blockGroupBytes,SubexpBlockAssembly.encodeList_eq_records]
    simp only [groupRecords,List.map_map,Function.comp_def]
  have hbareLocal := closeBare_measured 6 4 (rg 0) (rg 1) (rg 2) rest ctx.zero ctx.one groupBuffers
  change Eval (SubexpBlockAssembly.closeBare 21 17) _ _ _ at hbareLocal
  have hb := base_eval ctx rg rest rest groupBuffers
    (SubexpBlockAssembly.bareUpdate 6 4 groupBuffers) [] [] [] [] captured false false (rg 2)
    hbareLocal
  let blockBuffers := SubexpBlockAssembly.emit 4 (SubexpBlockAssembly.encodeBlock out.prepared) buffers
  have hbare : SubexpBlockAssembly.bareUpdate 6 4 groupBuffers = blockBuffers := by
    have h6' : afterWeight 6 = [] := by simpa [afterWeight,SubexpBlockAssembly.emit] using h6
    rw [SubexpBlockAssembly.bareUpdate_emitted 6 4 afterWeight groupRecords h6',hgroupBytes]
    exact SubexpBlockAssembly.emit_emit 4 (Encoding.frame weight.literal) (blockGroupBytes groups) buffers
  rw [hbare] at hb
  let rp := flags rg false false (rg 2)
  have hpackLocal := packComplete_measured 4 5 (rp 0) (rp 1) (rp 2) rest ctx.zero ctx.one blockBuffers
  change Eval (SubexpBlockAssembly.packComplete 17 18) _ _ _ at hpackLocal
  have hp := base_eval ctx rp rest rest blockBuffers
    (SubexpBlockAssembly.packUpdate 4 5 blockBuffers) [] [] [] [] captured false false true
    hpackLocal
  have hpacked : SubexpBlockAssembly.packUpdate 4 5 blockBuffers =
      SubexpBlockAssembly.emit 5
        (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeBlock out.prepared)) buffers :=
    SubexpBlockAssembly.packUpdate_emitted 4 5 buffers (SubexpBlockAssembly.encodeBlock out.prepared) h4
  rw [hpacked] at hp
  simp only [groupInput,encodeList_map] at hw
  have h := Eval.seq hw (Eval.seq hg (Eval.seq hb hp))
  norm_num [SubexpBlockAssembly.bufferPort] at h
  refine ⟨out,nw+(ng+(6*(groupBuffers 6).length+14+1+
    (13*(blockBuffers 4).length+15+1))),flags rp false false true,rfl,?_,?_⟩
  · have hgroupLen : (groupBuffers 6).length + 1 = (blockGroupBytes groups).length := by
      rw [←hgroupBytes]
      simp [groupBuffers,afterWeight,SubexpBlockAssembly.emit,h6]
    have hblockLen : (blockBuffers 4).length = (SubexpBlockAssembly.encodeBlock out.prepared).length := by
      simp [blockBuffers,SubexpBlockAssembly.emit,h4]
    change nw+(ng+(6*(groupBuffers 6).length+14+1+
      (13*(blockBuffers 4).length+15+1))) ≤
      captureBudget ctx a b.point.coordinates b.point.support records+
        40*SubexpSymbolicCost.indexBits ctx.dimension+160*ctx.target.length+110+
        scanSteps (fun ts => encodeGroup (ts.map TermData.template)) (groupBudget ctx a) b.groups groups+
        6*(blockGroupBytes groups).length+13*(SubexpBlockAssembly.encodeBlock out.prepared).length
    rw [hblockLen]
    omega
  · simpa only [blockBody,closeBare,packInto,BlockData.template,PointData.descriptor,
      encodeBlock,groupInput,encodeList_map,List.append_assoc] using h

end BlockExecution

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
