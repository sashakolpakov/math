import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramTables

namespace OAI.Algorithms

/-! Exact byte identities for the pure parameter package. These identify the
native interpolation producer outputs with the source bank cache fields. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters
open SubexponentialSAT BitProgram SubexpLiftRing IntegerRingLiftProgram

variable {r Q d : ℕ}

theorem inverseBytes_eq (p : SourceBank.Parameters r Q d) :
    InterpolationCacheProgram.inverseBytes p.t p.model p.modulus p.cache p.minusOne
      (LeafRingSetupProgram.nodeWords p.t d Q) =
      (List.ofFn (fun i : Fin Q => RingProgram.flat (p.inverse i))).flatten := by
  simp [InterpolationCacheProgram.inverseBytes,LeafRingSetupProgram.nodeWords,
    List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def,
    inverse,nodeCache,SourceCache.native]

theorem negativeBytes_eq (p : SourceBank.Parameters r Q d) :
    InterpolationCacheProgram.negativeBytes p.t p.model p.modulus p.cache p.minusOne
      (LeafRingSetupProgram.nodeWords p.t d Q) =
      (List.ofFn (fun i : Fin Q => RingProgram.flat (p.negative i))).flatten := by
  simp [InterpolationCacheProgram.negativeBytes,LeafRingSetupProgram.nodeWords,
    List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def,
    negative,nodeCache,SourceCache.native]

theorem differenceBytes_eq (p : SourceBank.Parameters r Q d) :
    InterpolationCacheProgram.differenceBytes p.t p.model p.modulus p.cache p.minusOne
      (LeafRingSetupProgram.nodeWords p.t d Q) =
      (List.ofFn (fun i : Fin Q =>
        (List.ofFn (fun j : Fin Q => RingProgram.flat (p.difference i j))).flatten)).flatten := by
  simp [InterpolationCacheProgram.differenceBytes,InterpolationCacheProgram.rowBytes,
    LeafRingSetupProgram.nodeWords,List.finRange,List.flatMap_def,List.map_ofFn,
    Function.comp_def,difference,nodeCache,SourceCache.native]

section Produced
variable (s : LeafHeadSetupProgram.Native.Inputs) (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (m : LeafParametersProgram.Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache u e) (hfield : s.Q < 3^(m.val 34))

/-- The source order is the layout order R; it does not depend on the later
shifted-target truncation cutoff or on the jet multiplicity. -/
theorem ofProduced_fields :
    let p := ofProduced s words hc m ht hd M cache u e hp hfield
    p.R=s.R ∧ p.hwords=words ∧ p.width=s.width ∧ p.power=s.power ∧ p.aWord=s.height ∧
    p.t=m.val 33 ∧ p.model=IrreducibleSearch.data hd ∧ p.modulus=M ∧ p.cache=cache := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem ofProduced_inverse :
    (ofProduced s words hc m ht hd M cache u e hp hfield).invDenom =
      LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd) M cache u s.R := rfl

theorem ofProduced_widths :
    let p := ofProduced s words hc m ht hd M cache u e hp hfield
    p.ringWidth=List.replicate (m.val 34*baseWidth 3 (m.val 33)) true ∧
      p.rowWidth=List.replicate (s.Q*(m.val 34*baseWidth 3 (m.val 33))) true :=
  ⟨rfl,rfl⟩

end Produced
end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters

end

end OAI.Algorithms
