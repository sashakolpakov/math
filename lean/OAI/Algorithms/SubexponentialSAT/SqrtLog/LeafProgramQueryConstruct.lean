import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPrepare

namespace OAI.Algorithms

/-! Existence of the actual query preparation requires no external size bound.
The finite model maxima below are used only for its measured execution budget. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram MulticolorTypes Subexp

def modelValueCap (m : Circuit.Model) : ℕ := Finset.univ.sup m.val
def modelLengthCap (m : Circuit.Model) : ℕ := Finset.univ.sup m.len

theorem modelValueCap_le (m : Circuit.Model) (V : ℕ) (h : ∀i,m.val i ≤ V) :
    modelValueCap m ≤ V := Finset.sup_le (fun i _ => h i)

theorem modelLengthCap_le (m : Circuit.Model) (L : ℕ) (h : ∀i,m.len i ≤ L) :
    modelLengthCap m ≤ L := Finset.sup_le (fun i _ => h i)

/-- The fixed frontend, packing, ring, interpolation, and denominator programs
produce the complete preparation directly from the physical input masters. -/
theorem construct (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hr : q.Ready a) (ho : q.OutputEmpty a) (hspare : PackingSpare a)
    (hg : Guard (q.input k)) (h728 : a.stacks 728=[])
    (W : ℕ) (hwidth : ∀i,(a.stacks i).length ≤ W) :
    ∃V L, ∃p : Preparation q k a hg W V L,
      V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) ∧
      L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) := by
  obtain ⟨nf,front,l,bw,w,tail,np,packed,hf,hfn,hfs,hn,hall,hp,hpn,hbytes,hbank,hframe,hregs,hw,hrows⟩ :=
    frontend_packing q k a hv hr ho hspare hg W hwidth
  let ms := Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)
  let V : ℕ := Finset.univ.sup ms.val
  let L : ℕ := Finset.univ.sup ms.len
  have hvalues (i : Fin 64) : ms.val i ≤ V := Finset.le_sup (Finset.mem_univ i)
  have hlengths (i : Fin 64) : ms.len i ≤ L := Finset.le_sup (Finset.mem_univ i)
  have hf728 : front.stacks 728=a.stacks 728 := hfs.frame _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  have hp728 : packed.stacks 728=[] :=
    (hframe _ (by decide) (by decide) (by decide)).trans (hf728.trans h728)
  have hcutoff := packed_cutoff (q.input k) l front packed (packingProblem q k hg) w tail
    (packing_empty front hfs.privateEmpty hfs.spare) hfs.exported hbytes
  obtain ⟨arithmeticData⟩ :=
    constructArithmetic packed (Execute.guardedModel (q.input k) l) bw (packed.regs ∘ Exports.bankRegs)
      hfs.shape hbank _ V L hw hvalues hlengths
      (ring_precision_pos (q.input k) l hg) (ring_degree_pos (q.input k) l hg)
      (ring_exponent (q.input k) l hg) hp728
  let p : Preparation q k a hg W V L := {
    lengths := l, bankWords := bw, front := front, frontSteps := nf,
    frontExecution := hf, frontTime := hfn, frontOutput := hfs,
    firstWord := w, remainingWords := tail, alphabetOrder := hrows,
    alphabetNodup := hn, alphabetComplete := hall,
    packed := packed, packingSteps := np, packingExecution := hp, packingTime := hpn,
    packingBytes := hbytes, packingFrame := hframe, packingRegisters := hregs, cutoff := hcutoff,
    arithmeticData := arithmeticData }
  exact ⟨V,L,p,rfl,rfl⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
