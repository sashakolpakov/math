import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReadyInput

namespace OAI.Algorithms

/-! Derivation of the source-bank invariant from its paid master copies.
The source numerator sees empty 5/10 only inside the checked staging wrapper. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

structure BankFields {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (s : Fin 320 → List Bool) : Prop where
  colors : s 21=List.replicate r true
  nodes : s 22=List.replicate Q true
  index : s 25=[true]
  typeWidth : s 26=List.replicate (Q*r) true
  positive : s 42=p.saved.hp
  negative : s 43=p.saved.hn
  scalarWidth : s 44=p.width
  power : s 45=p.power.1
  radius : s 47=List.replicate p.R true
  offset : s 48=p.aWord
  zeroCache : s 249=RingProgram.flat p.ops.zeroRun.1
  oneCache : s 250=RingProgram.flat p.ops.oneRun.1
  minusCache : s 251=RingProgram.flat p.minusOne
  inverseDenominator : s 252=RingProgram.flat p.invDenom
  inverses : s 308=(List.ofFn (fun i => RingProgram.flat (p.inverse i))).flatten
  negatives : s 309=(List.ofFn (fun i => RingProgram.flat (p.negative i))).flatten
  differences : s 310=(List.ofFn (fun i => (List.ofFn (fun j => RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : s 311=p.ringWidth
  rowWidth : s 312=p.rowWidth
  zero : s 313=RingProgram.flat p.ops.zeroRun.1
  one : s 314=RingProgram.flat p.ops.oneRun.1

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.bank_fields (h : Input p ps P a v N f S) (D W : ℕ) :
    BankFields p (bank a D W ps v N f).stacks := by
  have cp (src : Fin 768) (dst : Fin 320)
      (hp : (src,localPort (sourcePorts dst)) ∈ SourceControls.pairs)
      (hi : dst ∉ ([5,10,192,193,242,243,304] : List (Fin 320))) :
      (bank a D W ps v N f).stacks dst=a.stacks src :=
    (bank_frame a D W ps v N f dst hi).trans (h.copied src _ hp)
  exact ⟨(cp 130 21 (by decide) (by decide)).trans h.colors,
    (cp 131 22 (by decide) (by decide)).trans h.nodes,
    (bank_frame a D W ps v N f 25 (by decide)).trans h.delta,
    (cp 132 26 (by decide) (by decide)).trans h.typeWidth,
    (cp 710 42 (by decide) (by decide)).trans h.positive,
    (cp 711 43 (by decide) (by decide)).trans h.negative,
    (cp 140 44 (by decide) (by decide)).trans h.scalarWidth,
    (cp 712 45 (by decide) (by decide)).trans h.power,
    (cp 138 47 (by decide) (by decide)).trans h.radius,
    (cp 139 48 (by decide) (by decide)).trans h.offset,
    (cp 280 249 (by decide) (by decide)).trans h.zero,
    (cp 207 250 (by decide) (by decide)).trans h.one,
    (cp 211 251 (by decide) (by decide)).trans h.minusOne,
    (cp 728 252 (by decide) (by decide)).trans h.inverseDenominator,
    (cp 713 308 (by decide) (by decide)).trans h.inverses,
    (cp 714 309 (by decide) (by decide)).trans h.negatives,
    (cp 715 310 (by decide) (by decide)).trans h.differences,
    (cp 717 311 (by decide) (by decide)).trans h.ringWidth,
    (cp 716 312 (by decide) (by decide)).trans h.rowWidth,
    (cp 280 313 (by decide) (by decide)).trans h.zero,
    (cp 207 314 (by decide) (by decide)).trans h.one⟩

theorem Input.bank_input (h : Input p ps P a v N f S) (D W : ℕ)
    (u y : UniversalType r Q 1) :
    SourceBank.InputFields (bank a D W ps v N f) p.saved p.start u y := by
  have F := h.bank_fields D W
  have E := h.bank_empty D W
  intro i hi hj
  fin_cases i
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 0 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 1 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 2 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 3 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 4 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 5 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 6 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 7 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 8 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 9 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 10 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 11 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 12 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 13 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 14 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 15 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 16 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 17 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 18 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 19 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 20 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.colors
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.nodes
  · exact False.elim (hi rfl)
  · exact False.elim (hj rfl)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.index
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.typeWidth
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 27 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 28 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 29 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 30 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 31 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 32 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 33 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 34 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 35 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 36 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 37 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 38 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 39 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 40 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 41 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.positive
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.negative
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.scalarWidth
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.power
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 46 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.radius
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.offset
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 49 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 253 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 254 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 52 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 53 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 54 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 55 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 56 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 57 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 58 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 59 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 60 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 61 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 62 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 63 (by decide)

theorem Input.bank_work (h : Input p ps P a v N f S) (D W : ℕ) :
    SourceBank.WorkReady (bank a D W ps v N f) := by
  have E := h.bank_empty D W
  refine ⟨?_,E 319 (by decide),E 287 (by decide),E 37 (by decide),
    E 64 (by decide),E 65 (by decide),?_⟩
  · intro j hj _
    apply E
    simp only [SourceBank.cleanupPorts, List.mem_append] at hj
    rcases hj with ((hj | hj) | hj) | hj
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [bankBlank, localBlank, physicalLive, changedLocal,
          LayoutSourceRowsProgram.sourcePorts]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
      fin_cases k <;> simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
      fin_cases k <;> simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl <;>
        simp [bankBlank, localBlank, physicalLive, changedLocal,
          LayoutSourceRowsProgram.sourcePorts]
  · intro j hj
    apply E
    have hv : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by omega
    rcases hv with hv|hv|hv|hv
    · have he : j=(0 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · have he : j=(1 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · have he : j=(2 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · have he : j=(3 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]

theorem Input.bank_ring (h : Input p ps P a v N f S) (D W : ℕ) :
    IntegerRingLiftProgram.CachedReady p.t p.model p.modulus p.cache
      p.ops.zeroRun.1 p.ops.oneRun.1 p.minusOne (SourceBank.lowStore (bank a D W ps v N f)) := by
  let b := bank a D W ps v N f
  have F := h.bank_fields D W
  have E := h.bank_empty D W
  have H := h.arithmetic.scalarReady
  have hf (i : Fin 256) (hlo : 120 ≤ i.val) (hhi : i.val ≤ 204)
      (h192 : i≠192) (h193 : i≠193) :
      SourceBank.lowStore b i=rawLow a i := by
    have hx : SourceBank.vectorPorts i ∉ ([5,10,192,193,242,243,304] : List (Fin 320)) := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
      repeat' constructor
      all_goals intro he; have hh := congrArg Fin.val he
      all_goals simp only [SourceBank.vectorPorts,Fin.val_castAdd] at hh
      all_goals omega
    change b.stacks (SourceBank.vectorPorts i)=_
    rw [bank_frame a D W ps v N f _ hx]
    exact arithmetic_frame a i ⟨Or.inr (Or.inr ⟨by omega,hhi⟩),h192,h193⟩
  have hn : HornerProgram.Services.NativeReady 3 p.t p.modulus p.cache
      (HornerProgram.modelTable p.t p.model p.modulus p.cache) (SourceBank.lowStore b) := by
    refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_⟩
    · rw [hf 120 (by decide) (by decide) (by decide) (by decide)]; exact H.workspace.1
    · intro i
      have hv := hf (ReconstructionProgram.RingAdapter.ports i)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      rw [hv]
      simpa only [ReconstructionProgram.RingAdapter.finalNative,
        hf 194 (by decide) (by decide) (by decide) (by decide),
        hf 201 (by decide) (by decide) (by decide) (by decide),
        hf 202 (by decide) (by decide) (by decide) (by decide),
        hf 203 (by decide) (by decide) (by decide) (by decide)] using H.workspace.2 i
    · rw [hf 194 (by decide) (by decide) (by decide) (by decide)]; exact H.modulus
    · rw [hf 202 (by decide) (by decide) (by decide) (by decide)]; exact H.width
    · rw [hf 203 (by decide) (by decide) (by decide) (by decide)]; exact H.zero
    · rw [hf 201 (by decide) (by decide) (by decide) (by decide)]; exact H.table
    · rw [hf 204 (by decide) (by decide) (by decide) (by decide)]; exact H.degree
  exact ⟨hn,⟨E 120 (by decide),E 240 (by decide),E 241 (by decide),E 244 (by decide),
    E 245 (by decide)⟩,F.zeroCache,F.oneCache,F.minusCache,
    E 246 (by decide),E 247 (by decide),E 248 (by decide),E 255 (by decide)⟩

theorem Input.bank_ready (h : Input p ps P a v N f S) (D W : ℕ) :
    SourceBank.Ready p (bank a D W ps v N f) := by
  have F := h.bank_fields D W
  exact ⟨h.bank_work D W,h.bank_input D W,h.bank_ring D W,F.inverseDenominator,
    by simp [F.nodes],by simp [F.radius],F.inverses,F.negatives,F.differences,
    F.ringWidth,F.rowWidth,F.zero,F.one⟩

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
