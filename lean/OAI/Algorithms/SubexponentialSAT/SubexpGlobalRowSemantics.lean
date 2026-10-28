import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowService
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowComputedSource
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowScalarDecode

namespace OAI.Algorithms

/-!
# Polynomial meaning of the actual global row output

The packing lookup selects the same constant or universal source expression
as the fixed row program. Its complete source coefficients are evaluated
before the selected residue section is applied. Every polynomial identity
below follows from individual cache values and the checked coefficient
search; no desired row, degree bound, or output equality is assumed.
-/

namespace SubexponentialSAT.SubexpGlobalRowSemantics

open SubexpLiftRing SubexpQuarticRing SubexpSelectedConversions
open SubexpRepresentedRows SubexpRowInterpolation SubexpTaylorExecution
open Subexp.ConstructivePacking MulticolorTypes

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (xs : List (ZMod p))
variable (inverse negative : Fin Q → List Bool)
variable (difference : Fin Q → Fin Q → List Bool)

/-- Typed interpretation of exactly the expression selected by the physical
packing branches. It contains the actual correction-array values. -/
def expressionAt (P : PackingData (Fin D) (UniversalType r Q Δ))
    (i : Fin Δ) (v w : Fin D) : SubexpGlobalRowEvaluation.Expression p :=
  match P.lookup v with
  | none => SubexpGlobalRowConstants.expression source (decide (v.val = w.val))
  | some (block, u) =>
    match P.lookup w with
    | none => SubexpGlobalRowConstants.expression source false
    | some (other, y) =>
      if block = other then
        SubexpGlobalRowValues.expression source i u y xs inverse negative difference
      else SubexpGlobalRowConstants.expression source false

/-- The coefficient list whose bytes the physical row service returns. -/
def coefficientsAt (μ : ℕ) (P : PackingData (Fin D) (UniversalType r Q Δ))
    (i : Fin Δ) (v w : Fin D) : List (Quad (Word (baseWidth p μ))) :=
  SubexpCoefficientLiftArray.liftedArray p μ source.modulus
    (SubexpRowToTaylorCalls.evaluated source xs.length
      (expressionAt source xs inverse negative difference P i v w))

theorem outputAt_eq (μ : ℕ) (P : PackingData (Fin D) (UniversalType r Q Δ))
    (i : Fin Δ) (v w : Fin D) :
    SubexpGlobalRowService.outputAt μ source xs inverse negative difference P i v w =
      SubexpRowToTaylorCalls.output μ source xs.length
        (expressionAt source xs inverse negative difference P i v w) := by
  cases hv : P.lookup v with
  | none =>
      simp only [SubexpGlobalRowService.outputAt, expressionAt, hv]
      rfl
  | some a =>
      rcases a with ⟨block, u⟩
      cases hw : P.lookup w with
      | none =>
          simp only [SubexpGlobalRowService.outputAt, expressionAt, hv, hw]
          rfl
      | some b =>
          rcases b with ⟨other, y⟩
          by_cases h : block = other
          · simp only [SubexpGlobalRowService.outputAt, expressionAt, hv, hw, h, ite_eq_left]
            rfl
          · simp only [SubexpGlobalRowService.outputAt, expressionAt, hv, hw, h]
            rfl

/-- The table traversal reverses the service's stack payload back to this
forward coefficient encoding. No decoding/re-encoding assumption occurs. -/
theorem outputAt_forward (μ : ℕ) (P : PackingData (Fin D) (UniversalType r Q Δ))
    (i : Fin Δ) (v w : Fin D) :
    (SubexpGlobalRowService.outputAt μ source xs inverse negative difference P i v w).reverse =
      SubexpCoefficientLiftArray.encodeArray
        (coefficientsAt source xs inverse negative difference μ P i v w) := by
  rw [outputAt_eq]
  simp only [SubexpRowToTaylorCalls.output, List.reverse_reverse, coefficientsAt]

variable (cache : NodeCache (SubexpSymbolicCost.QuarticCode p 0) Q)
variable {node : Fin Q → SubexpActualRing.E p} (units : NodeUnits node)
variable (hnode : ∀ j, source.residueRing.decode (cache.node j) = node j)
variable (hinv : ∀ j, source.residueRing.decode (cache.inverse j) = units.nodeInverse j)
variable (hdiff : ∀ j k,
  source.residueRing.decode (cache.difference j k) = units.differenceInverse j k)
variable (hinverse : ∀ j, SubexpRawRow.scalarDecode source (inverse j) =
  source.residueRing.decode (cache.inverse j))
variable (hnegative : ∀ j, SubexpRawRow.scalarDecode source (negative j) =
  source.residueRing.decode ((source.residueRing.negRun (cache.node j)).1))
variable (hdifference : ∀ j k, SubexpRawRow.scalarDecode source (difference j k) =
  source.residueRing.decode (cache.difference j k))

include hnode hinv hdiff hinverse hnegative hdifference in
theorem values_denote (A R : ℕ) (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (i : Fin Δ) (u y : UniversalType r Q Δ) :
    ((SubexpGlobalRowValues.expression source i u y xs inverse negative difference).map
      (SubexpRowSourceSemantics.denote source)).eval =
      (mapCode source.residueRing.decode
        (Subexp.ComputedRowSource.universalCode source.program cache embedCode R
          (Subexp.CoefficientSearch.coefficientsNat p A R) u i y)).denote := by
  rw [SubexpGlobalRowValues.expression_denote]
  have hdelta : SubexpRawRow.scalarDecode source
      (if u = y then SubexpFlatAdd.encode source.one else SubexpFlatAdd.encode source.zero) =
      source.residueRing.decode
        (if u = y then source.residueRing.oneRun.1 else source.residueRing.zeroRun.1) := by
    by_cases h : u = y
    · simp only [ite_eq_left h]
      exact Subexp.UniversalRowScalarDecode.scalarDecode_encode source source.one
    · simp only [ite_eq_right h]
      exact Subexp.UniversalRowScalarDecode.scalarDecode_encode source source.zero
  have h := Subexp.UniversalRowComputedSource.row_eval_selected p i u y xs
    inverse negative difference source.residueRing cache units hnode hinv hdiff
    embedCode (embedCode_decode source) (SubexpRawRow.scalarDecode source)
    (Subexp.UniversalRowScalarDecode.scalarDecode_quartet source)
    hinverse hnegative hdifference A R hlength hcheck
    (if u = y then SubexpFlatAdd.encode source.one else SubexpFlatAdd.encode source.zero) hdelta
  rw [show Subexp.UniversalRowProgram.mapRow
      (fun bits => Polynomial.C (SubexpRawRow.scalarDecode source bits))
      (SubexpGlobalRowValues.rawRow source i u y xs inverse negative difference) =
    Subexp.UniversalRowSource.mapRow
      (fun bits => Polynomial.C (SubexpRawRow.scalarDecode source bits))
      (SubexpGlobalRowValues.rawRow source i u y xs inverse negative difference) by rfl]
  simpa only [SubexpGlobalRowValues.rawRow, Prepared.residueRing_program] using h

include hnode hinv hdiff hinverse hnegative hdifference in
theorem expressionAt_denote (A R : ℕ) (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (P : PackingData (Fin D) (UniversalType r Q Δ)) (i : Fin Δ) (v w : Fin D) :
    ((expressionAt source xs inverse negative difference P i v w).map
      (SubexpRowSourceSemantics.denote source)).eval =
      (mapCode source.residueRing.decode
        (Subexp.ComputedRowSource.globalCode source.program cache embedCode R
          (Subexp.CoefficientSearch.coefficientsNat p A R) P i v w)).denote := by
  change _ = (mapCode source.residueRing.decode
    (Subexp.ComputedRowSource.lookupCode source.residueRing.zeroRun.1 source.residueRing.oneRun.1 P
      (Subexp.ComputedRowSource.universalCode source.program cache embedCode R
        (Subexp.CoefficientSearch.coefficientsNat p A R)) i v w)).denote
  rw [Subexp.ComputedRowSource.lookupCode_decode]
  cases hv : P.lookup v with
  | none =>
      simp only [expressionAt, Subexp.ComputedLayout.rowValue, hv,
        SubexpGlobalRowConstants.expression_denote]
      by_cases h : w = v
      · subst w
        simp
      · have hval : v.val ≠ w.val := fun he => h (Fin.ext he.symm)
        simp [h, hval]
  | some a =>
      rcases a with ⟨block, u⟩
      cases hw : P.lookup w with
      | none =>
          simp only [expressionAt, Subexp.ComputedLayout.rowValue, hv, hw,
            SubexpGlobalRowConstants.expression_denote, Bool.false_eq_true, ↓reduceIte,
            Polynomial.C_0]
      | some b =>
          rcases b with ⟨other, y⟩
          by_cases h : block = other
          · simp only [expressionAt, Subexp.ComputedLayout.rowValue, hv, hw, ite_eq_left h]
            exact values_denote source xs inverse negative difference cache units
              hnode hinv hdiff hinverse hnegative hdifference A R hlength hcheck i u y
          · simp only [expressionAt, Subexp.ComputedLayout.rowValue, hv, hw, ite_eq_right h,
              SubexpGlobalRowConstants.expression_denote, Bool.false_eq_true, ↓reduceIte,
              Polynomial.C_0]

include hnode hinv hdiff hinverse hnegative hdifference in
/-- The degree bound is derived from the represented universal row and the
actual packing branches, rather than supplied by the caller. -/
theorem expressionAt_degree (A R : ℕ) (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (P : PackingData (Fin D) (UniversalType r Q Δ)) (i : Fin Δ) (v w : Fin D) :
    ((expressionAt source xs inverse negative difference P i v w).map
      (SubexpRowSourceSemantics.denote source)).eval.natDegree ≤ R := by
  rw [expressionAt_denote source xs inverse negative difference cache units
    hnode hinv hdiff hinverse hnegative hdifference A R hlength hcheck]
  change (mapCode source.residueRing.decode
    (Subexp.ComputedRowSource.globalCode source.residueRing.program cache embedCode R
      (Subexp.CoefficientSearch.coefficientsNat p A R) P i v w)).denote.natDegree ≤ R
  rw [Subexp.ComputedRowSource.globalCode_decode source.residueRing cache units
    hnode hinv hdiff embedCode (embedCode_decode source)]
  exact Layout.assembledRow_degree _ _
    (fun u i y => SubexpAnnihilation.universalRow_degree
      (algebraMap (ZMod p) (SubexpActualRing.E p)) u i R
      (Subexp.CoefficientSearch.coefficientsNat p A R) units y) i v w

include hnode hinv hdiff hinverse hnegative hdifference in
/-- The coefficients in the actual returned payload give the complete
selected lift of the global source row. -/
theorem coefficientsAt_denote (A R : ℕ) (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (μ : ℕ) (hμ : 0 < μ) (P : PackingData (Fin D) (UniversalType r Q Δ))
    (i : Fin Δ) (v w : Fin D) :
    PolynomialAlgorithm.denote
      ((coefficientsAt source xs inverse negative difference μ P i v w).map
        (SubexpRowLiftSemantics.targetDecode p μ)) =
      SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R
        (mapCode source.residueRing.decode
          (Subexp.ComputedRowSource.globalCode source.program cache embedCode R
            (Subexp.CoefficientSearch.coefficientsNat p A R) P i v w)).denote := by
  have hd := expressionAt_degree source xs inverse negative difference cache units
    hnode hinv hdiff hinverse hnegative hdifference A R hlength hcheck P i v w
  have h := SubexpRowToTaylor.output_denote p μ source xs.length hμ
    (expressionAt source xs inverse negative difference P i v w)
    (by simpa only [hlength] using hd)
  change PolynomialAlgorithm.denote
    ((coefficientsAt source xs inverse negative difference μ P i v w).map
      (SubexpRowLiftSemantics.targetDecode p μ)) = _ at h
  rw [expressionAt_denote source xs inverse negative difference cache units
    hnode hinv hdiff hinverse hnegative hdifference A R hlength hcheck, hlength] at h
  exact h

include hnode hinv hdiff hinverse hnegative hdifference in
/-- Specializing to the prepared counting ring identifies the exact
`liftCode` used by the concrete factor source. -/
theorem coefficientsAt_denote_liftCode (A R : ℕ) (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    {N : ℕ} (target : Prepared p N)
    (P : PackingData (Fin D) (UniversalType r Q Δ)) (i : Fin Δ) (v w : Fin D) :
    PolynomialAlgorithm.denote
      ((coefficientsAt source xs inverse negative difference (N + 1) P i v w).map
        target.ring.decode) =
      (mapCode target.ring.decode
        (liftCode source.program target.program (betaLift source N) R
          (Subexp.ComputedRowSource.globalCode source.program cache embedCode R
            (Subexp.CoefficientSearch.coefficientsNat p A R) P i v w))).denote := by
  calc
    _ = SubexpExplicitLift.liftPolynomial
        (SubexpActualRing.sectionValue p (N + 1) (Nat.succ_pos N)) R
        (mapCode source.residueRing.decode
          (Subexp.ComputedRowSource.globalCode source.program cache embedCode R
            (Subexp.CoefficientSearch.coefficientsNat p A R) P i v w)).denote :=
      coefficientsAt_denote source xs inverse negative difference cache units
        hnode hinv hdiff hinverse hnegative hdifference A R hlength hcheck
        (N + 1) (Nat.succ_pos N) P i v w
    _ = _ := by
      symm
      exact liftCode_decode source.residueRing target.ring (betaLift source N)
        (SubexpActualRing.sectionValue p (N + 1) (Nat.succ_pos N))
        (betaLift_decode source target) R _

end SubexponentialSAT.SubexpGlobalRowSemantics

end OAI.Algorithms
