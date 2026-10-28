import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramRowCode
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTableSource
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceProgram

namespace OAI.Algorithms

/-! The physical Lagrange row-source emitter instantiated with integer-derived
ring scalars. Its inputs are scalar arrays, not a preassembled polynomial or
instruction stream. Upstream proofs must supply the scalar arrays and their
individual decode laws; the concrete emitter itself is fully traced. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpRowInterpolation
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpTaylorExecution
open SubexponentialSAT.Subexp
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open LayoutScaledMatrices

variable {C O : Type*} [CommRing O] {r Q Δ : ℕ}
variable (ops : RepresentedRing C O) (cache : NodeCache C Q)
variable (integerWord : ℤ → C) (hinteger : ∀ z, ops.decode (integerWord z) = (z : O))
variable (denominator : Oˣ) (inverseDenominator : C)
variable (hinverse : ops.decode inverseDenominator = (↑(denominator⁻¹) : O))
variable {node : Fin Q → O} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hnodeInv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)
variable (decode : List Bool → O) (tables : UniversalRowLoop.Tables)
variable (A R : ℕ) (u y : UniversalType r Q Δ) (i : Fin Δ)
variable (delta limit : List Bool)
variable (hvalue : ∀ t : Fin Q, decode (tables.values.getD t.val []) =
  ops.decode (sourceValue ops.program integerWord inverseDenominator A R u i y t))
variable (hinverses : ∀ t : Fin Q, decode (tables.inverses.getD t.val []) =
  ops.decode (cache.inverse t))
variable (hdifferences : ∀ t s : Fin Q,
  decode ((tables.differences.getD t.val []).getD s.val []) =
  ops.decode (cache.difference t s))
variable (hnegatives : ∀ t : Fin Q, decode (tables.negatives.getD t.val []) =
  ops.decode ((ops.negRun (cache.node t)).1))
variable (hdelta : decode delta = ops.decode (if u = y then ops.oneRun.1 else ops.zeroRun.1))
variable (hlimit : limit.length = R)

include hinteger hinverse hnode hnodeInv hdiff hvalue hinverses hdifferences hnegatives hdelta hlimit in
theorem tableSource_eq :
    (UniversalRowProgram.rowExpression Polynomial.X
      (UniversalRowSource.mapRow (fun bits => Polynomial.C (decode bits))
        (UniversalRowDataProgram.row tables
          (UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y))
          delta limit))).eval =
      sourceRow (LayoutNumerator.family r Q Δ A R) denominator u i R units y := by
  rw [UniversalRowTableSource.row_eval_of_decode cache tables ops units
    hnode hnodeInv hdiff decode u (fun v => v.head) (u.slot i) R
    (sourceValue ops.program integerWord inverseDenominator A R u i) y delta limit
    hvalue hinverses hdifferences hnegatives hdelta hlimit]
  exact sourceCode_decode ops integerWord hinteger denominator inverseDenominator hinverse
    cache units hnode hnodeInv hdiff A R u i y

include hinteger hinverse hnode hnodeInv hdiff hvalue hinverses hdifferences hnegatives hdelta hlimit in
/-- Real source construction plus its exact ring-valued polynomial meaning.
The scalar-table producer is deliberately not hidden inside this theorem. -/
theorem emitSource_runsIn (width rowWidth zero one : List Bool)
    (a : UniversalRowGather.Data)
    (valid : UniversalRowLoop.Valid tables width rowWidth
      (UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y)))
    (ready : UniversalRowLoop.ready tables width rowWidth
      (UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y)) a)
    (ha18 : a.stacks 18 = delta) (ha13 : a.stacks 13 = limit)
    (ha3 : a.stacks 3 = zero) (ha10 : a.stacks 10 = one)
    (ha14 : a.stacks 14 = []) (ha17 : a.stacks 17 = []) (ha31 : a.stacks 31 = []) :
    ∃ b : UniversalRowGather.Data,
      RunsIn UniversalRowSourceProgram.program
        (UniversalRowSourceProgram.bound tables width rowWidth
          (UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y))
          delta limit zero one)
        (a.withPC (some UniversalRowSourceProgram.program.entry)) (b.withPC none) ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.rowCode zero one (zero ++ one)
          (UniversalRowDataProgram.row tables
            (UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y))
            delta limit)) ∧
      (UniversalRowProgram.rowExpression Polynomial.X
        (UniversalRowSource.mapRow (fun bits => Polynomial.C (decode bits))
          (UniversalRowDataProgram.row tables
            (UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y))
            delta limit))).eval =
        sourceRow (LayoutNumerator.family r Q Δ A R) denominator u i R units y := by
  let positions := UniversalRowTableSource.positions
    (mismatchPositions (fun v => v.head) (u.slot i) y)
  have hvalid : UniversalRowLoop.Valid tables width rowWidth positions := by
    simpa [positions] using valid
  have hready : UniversalRowLoop.ready tables width rowWidth positions a := by
    simpa [positions] using ready
  obtain ⟨b,hb,hs⟩ := UniversalRowSourceProgram.program_runsIn tables width rowWidth
    positions hvalid delta limit zero one a hready ha18 ha13 ha3 ha10 ha14 ha17 ha31
  refine ⟨b,by simpa [positions] using hb,by simpa [positions] using hs,?_⟩
  apply tableSource_eq (ops := ops) (cache := cache) (integerWord := integerWord)
    (denominator := denominator) (inverseDenominator := inverseDenominator)
    (units := units) (decode := decode) (tables := tables) (A := A) (R := R)
    (u := u) (y := y) (i := i) (delta := delta) (limit := limit)
  all_goals assumption

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
