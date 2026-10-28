import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeSource

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds
open LayoutProgram RowSelectionProgram

structure InputBounds (s : Native.Inputs) (B : ℕ) : Prop where
  n : s.n ≤ B
  D : s.D ≤ B
  r : s.r ≤ B
  Q : s.Q ≤ B
  R : s.R ≤ B
  width : s.width.length ≤ B
  height : s.height.length ≤ B
  metadata : s.metadata.length ≤ B
  plans : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B
  Qr : s.Q*s.r ≤ B

theorem inputBounds (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (h : Native.Ready s a) (B : ℕ) (hb : WordBound B a) : InputBounds s B := by
  have hp : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B := by simpa only [h.plans] using hb 136
  have hc := Encoding.length_encodeList_lower (fun p : ℕ×ℕ => LayoutOwnerFiberProgram.pairPayload p.1 p.2) s.plans
  have hd : s.D ≤ B := by
    change s.plans.length+1 ≤ (LayoutOwnerFiberProgram.stream s.plans).length at hc
    rw [s.plans_length] at hc
    omega
  exact ⟨by simpa [h.ambient,unary] using hb 128,hd,
    by simpa [h.colors,unary] using hb 130,by simpa [h.nodes,unary] using hb 131,
    by simpa [h.order,unary] using hb 138,by simpa only [h.width] using hb 140,
    by simpa only [h.height] using hb 139,by simpa only [h.metadata] using hb 135,hp,
    by simpa [h.wordWidth,unary] using hb 132⟩

def entryEnvelope (X : ℕ) : ℕ :=
  800*(2*X+1)^2+1+10000000000000*(X+1)^5+550*(X*X+11*X+1)+450*(100*(X+1)^2)+1200

def columnEnvelope (X : ℕ) : ℕ :=
  1000*(2*X+1)^2+18*X+2*X+39+
    X*(entryEnvelope X+5*X+12+25000*((X+1)*(100*(X+1)^2+2)+3)^2+9*(100*(X+1)^2+2))

theorem columns_le {s : Native.Inputs} {B : ℕ} (h : InputBounds s B) :
    s.columnTime ≤ columnEnvelope (B+1) ∧ s.columnLength ≤ (B+1)*(100*(B+2)^2+2) := by
  let X := B+1
  have hx : B ≤ X := by dsimp [X]; omega
  have hn := h.n.trans hx
  have hd := h.D.trans hx
  have hr := h.r.trans hx
  have hq := h.Q.trans hx
  have ho := h.R.trans hx
  have hw := h.width.trans hx
  have hh := h.height.trans hx
  have hm := h.metadata.trans hx
  have hp := h.plans.trans hx
  have hqr := h.Qr.trans hx
  have hpower : s.power.1.length ≤ X := by
    simp only [Native.Inputs.power,IntegerCache.denominatorWord,List.length_append,
      List.length_replicate,List.length_singleton]
    dsimp [X]
    omega
  have hpair : pairLength s.power ≤ X := by
    simpa only [pairLength,Native.Inputs.power,List.length_nil,Nat.add_zero] using hpower
  have hlen : s.entryLength ≤ 100*(X+1)^2 := integerLength_le _ _ _ _ X ho hw hpair hpower
  have hib := integerBudget_le _ _ _ _ _ _ _ X hr hq hh ho hw hpair hpower
  have hs : s.size ≤ X*X+11*X+1 := by
    unfold Native.Inputs.size
    have hm := Nat.mul_le_mul ho hw
    omega
  have he : s.entryTime ≤ entryEnvelope X := by
    unfold Native.Inputs.entryTime Native.Inputs.lookupTime LayoutFiberSumProgram.nativeTime entryEnvelope
    have hu : 800*(s.metadata.length+s.D+1)^2+1 ≤ 800*(2*X+1)^2+1 := by gcongr ; omega
    dsimp only [Native.Inputs.entryLength] at hlen
    omega
  constructor
  · change s.columnTime ≤ columnEnvelope X
    unfold Native.Inputs.columnTime columnEnvelope
    gcongr ; omega
  · change s.D*(s.entryLength+2) ≤ X*(100*(X+1)^2+2)
    gcongr

/-- One deliberately coarse fixed polynomial pays both native column costs. -/
theorem columnEnvelope_le (X : ℕ) : columnEnvelope X ≤ 10000000000000000*(X+1)^8 := by
  have hp (j : ℕ) (hj : j ≤ 8) : X^j ≤ (X+1)^8 :=
    (Nat.pow_le_pow_left (Nat.le_succ X) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have h0 : 1 ≤ (X+1)^8 := by simpa using hp 0 (by decide)
  have h1 : X ≤ (X+1)^8 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  dsimp only [columnEnvelope,entryEnvelope]
  conv_lhs => ring_nf
  omega

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
