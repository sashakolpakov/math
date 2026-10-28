import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpInputBitProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorRowCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpSourceReference
import OAI.Algorithms.SubexponentialSAT.SubexpMomentStep
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentProducer
import OAI.Algorithms.SubexponentialSAT.SubexpScalarLiteralProgram

namespace OAI.Algorithms

/-! Finite factor data and its local polynomial meaning. The same source rows,
residue origins, tables, and cache coefficients determine the physical packet
and the reference factor. Runtime packet assembly is in the companion module. -/

namespace SubexponentialSAT.SubexpFactorPacketProvenance

open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost
open SubexpSelectedConversions SubexpInputBitProgram

abbrev Code (p D : ℕ) := QuarticCode p D
abbrev Raw (p D : ℕ) := SymbolicCost.CoeffList D (Code p D)
abbrev Ring (p D : ℕ) [Fact p.Prime] := SubexpActualRing.Ring p (D+1)

/-- The local finite data used by one factor. The source degree certificate
is required only for the semantic theorem, not to form or execute a packet. -/
structure Input (p D labels arity degree : ℕ) where
  cache : List (List (Code p D))
  rows : List (SubexpTableInterpolation.Row labels arity (Code p D))
  origins : Fin arity → Fin D → ResidueCode p
  sourceRows : Fin arity → Fin D → SubexpTaylorRowCorrectness.RowExpr p

/-- A list of these packets may contain factors with different scopes and
source degree bounds. -/
structure Packet (p D : ℕ) where
  labels : ℕ
  arity : ℕ
  degree : ℕ
  input : Input p D labels arity degree

noncomputable abbrev decode (p D : ℕ) [Fact p.Prime] : Code p D → Ring p D :=
  SubexpHornerMachine.decode p (D+1) (QuarticSearch.liftedCoefficients p (D+1))

variable {p D labels arity degree : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (target : Prepared p D)
variable (theta : Code p D)
variable (minusOne : Word (baseWidth p (D+1))) (point : Fin D → ResidueCode p)
variable (input : Input p D labels arity degree)

def taylor (i : Fin arity) (j : Fin (degree+1)) (w : Fin D) : Code p D :=
  SubexpTaylorRowCorrectness.entry p (D+1) source target.modulus target.reduction theta
    degree (degree+1) (input.sourceRows i w) j

def columns (i : Fin arity) : List (List (List Bool)) :=
  (SubexpTaylorRowCorrectness.columns p (D+1) source target.modulus target.reduction theta
    degree (degree+1) (input.sourceRows i)).map (List.map SubexpQuarticFlatNeg.flat)

theorem columns_eq (i : Fin arity) :
    columns source target theta input i = List.ofFn (fun w => List.ofFn (fun j =>
      SubexpQuarticFlatNeg.flat (taylor source target theta input i j w))) := by
  exact SubexpTaylorRowCorrectness.column_bits_eq p (D+1) source target.modulus
    target.reduction theta degree (degree+1) (input.sourceRows i)

def argument (i : Fin arity) : Raw p D :=
  (SubexpColumnArgumentCode.compileColumns (betaOutput source (input.origins i) point)
    (SubexpQuarticNegMachine.negateWords p (D+1) target.modulus minusOne
      (betaOutput source (input.origins i) point))
    (taylor source target theta input i)).reverse

def factor : SubexpBlockAssemblySemantics.Factor (Code p D) (Raw p D) where
  labels := labels
  arity := arity
  cache := input.cache
  inputs := argument source target theta minusOne point input
  rows := input.rows

theorem serialize_raw (raw : Raw p D) :
    Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm SubexpQuarticFlatNeg.flat) raw =
      SubexpDenseSerialization.encodeFixedQuarticCoefficients p D raw := by
  have hf : (SubexpQuarticFlatNeg.flat : Code p D → List Bool) = SubexpFlatAdd.encode := by
    funext a
    exact SubexpHornerMachine.flat_eq_encode a
  rw [hf, ← SubexpMomentStep.encodedRecords_bytes]
  induction raw with
  | nil => rfl
  | cons term rest ih =>
      change true :: (Encoding.frame
        (SubexpArgumentEmitLoop.serializeTerm SubexpFlatAdd.encode term) ++
          Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm SubexpFlatAdd.encode) rest) = _
      rw [ih]
      rfl

theorem scalar_bytes (a : Code p D) :
    SubexpDenseSerialization.encodeFixedQuarticCoefficients p D
        (SubexpWeightCode.rawScalar D a) =
      SubexpScalarLiteralProgram.rawLiteral D (SubexpQuarticFlatNeg.flat a) := by
  rw [← serialize_raw]
  rfl

noncomputable section

def liftedRow (i : Fin arity) (w : Fin D) : Polynomial (Ring p D) :=
  SubexpExplicitLift.liftPolynomial
    (SubexpActualRing.sectionValue p (D+1) (Nat.succ_pos D)) degree
    (((input.sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval)

def beta (i : Fin arity) : Ring p D :=
  SubexpInputCode.beta (SubexpActualRing.residueSection p (D+1) (Nat.succ_pos D)).lift
    (fun w => source.residueRing.decode (input.origins i w))
    (fun w => source.residueRing.decode (point w))

theorem beta_decode (i : Fin arity) :
    target.ring.decode (betaOutput source (input.origins i) point) = beta source point input i := by
  change target.ring.decode (betaLift source D (dotOutput source (input.origins i) point)) = _
  rw [betaLift_decode]
  unfold beta SubexpInputCode.beta dotOutput
  congr 1
  exact SubexpDotControl.foldPairs_dot source.residueRing.decode
    (SubexpInputBitProgram.multiply source) (SubexpInputBitProgram.add source)
    (multiply_decode source) (add_decode source) source.zero source.residueRing.zero_correct
    (input.origins i) point

theorem argument_denote
    (hminusOne : wordValue p (D+1) minusOne = -1)
    (hdegree : ∀ i w,
      (((input.sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ degree)
    (i : Fin arity) :
    SymbolicCost.denote (SubexpSourceSemantics.decodeRaw (decode p D)
      (argument source target theta minusOne point input i)) =
      Counting.rowArgument (liftedRow source input i) (decode p D theta)
        (beta source point input i) degree := by
  have htaylor : ∀ j w, SubexpArgumentProducer.decode p (D+1)
      (QuarticSearch.liftedCoefficients p (D+1)) (taylor source target theta input i j w) =
      ((liftedRow source input i w).comp
        (Polynomial.X + Polynomial.C (decode p D theta))).coeff j.val := by
    intro j w
    exact SubexpTaylorRowCorrectness.entry_eq p (D+1) source target.modulus
      target.reduction theta (Nat.succ_pos D) target.reduction_spec
      degree (degree+1) (input.sourceRows i w) (hdegree i w) j
  have h := SubexpArgumentProducer.produced_rowArgument p (D+1) target.modulus minusOne
    hminusOne (QuarticSearch.liftedCoefficients p (D+1))
    (betaOutput source (input.origins i) point) (taylor source target theta input i)
    (decode p D theta) (liftedRow source input i) htaylor
  change SymbolicCost.denote (SubexpSourceSemantics.decodeRaw (decode p D)
      (argument source target theta minusOne point input i)) =
      Counting.rowArgument (liftedRow source input i) (decode p D theta)
        (decode p D (betaOutput source (input.origins i) point)) degree at h
  have hb : decode p D (betaOutput source (input.origins i) point) =
      beta source point input i := beta_decode source target point input i
  rw [hb] at h
  exact h

/-- The reference builder uses the decoded origins and the true shifted
row coefficients determined by the same finite source expressions. -/
def referenceData {r : ℕ} (color : Fin r) :
    SubexpProgramBuilder.FactorData D labels degree r (SubexpActualRing.E p) (Ring p D) where
  arity := arity
  color := color
  origin := fun i w => source.residueRing.decode (input.origins i w)
  taylor := fun i j w =>
    ((liftedRow source input i w).comp
      (Polynomial.X + Polynomial.C (decode p D theta))).coeff j.val
  table := input.rows.map (SubexpRepresentedBuilder.mapRow (decode p D))

/-- The reference-side factor determined by the same packet data. Naming it
keeps elaboration of the refinement statement local and predictable. -/
noncomputable def referenceFactor {r : ℕ} (color : Fin r) :
    SubexpBlockAssemblySemantics.Factor (Ring p D)
      (SymbolicCost.CoeffList D (Ring p D)) :=
  SubexpSourceReference.factor
    (SubexpActualRing.residueSection p (D+1) (Nat.succ_pos D)).lift
    (input.cache.map (List.map (decode p D)))
    (referenceData source theta input color)
    (fun w => source.residueRing.decode (point w))

/-- Pointwise equality between the executed factor packet and its
reference-side interpretation. -/
def FactorReference {r : ℕ} (color : Fin r) : Prop :=
  letI : One (Code p D) := ⟨target.one⟩
  SubexpSourceReference.FactorRel (D := D) (decode p D)
    (factor source target theta minusOne point input)
    (referenceFactor source theta point input color)

section Value

local instance : Zero (Raw p D) := ⟨[]⟩
local instance [One (Code p D)] : One (Raw p D) := ⟨SubexpAlgorithm.rawOne D⟩

/-- The factor value is derived from local scalar tables and the actual
beta/Taylor/Ce outputs. No factor-value or jet identity is a hypothesis. -/
theorem factor_value_eq
    (hminusOne : wordValue p (D+1) minusOne = -1)
    (hdegree : ∀ i w,
      (((input.sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ degree)
    (nodes : Fin labels → Ring p D) (hu : TableInterpolation.UnitDifferences nodes)
    (hcache : ∀ i : Fin labels,
      PolynomialAlgorithm.denote ((input.cache.map (List.map (decode p D))).getD i.val []) =
        TableInterpolation.basis nodes hu i)
    {σ : Type*} (ix : Fin arity ≃ σ) (table : MvPolynomial σ (Ring p D))
    (htable : SubexpTableInterpolation.tablePolynomial nodes hu
      (input.rows.map (SubexpRepresentedBuilder.mapRow (decode p D))) =
        MvPolynomial.rename ix.symm table) :
    letI : One (Code p D) := ⟨target.one⟩
    (((factor source target theta minusOne point input).expression
        (SubexpWeightCode.rawScalar D)).map
      (fun raw => SymbolicCost.denote (SubexpSourceSemantics.decodeRaw (decode p D) raw))).eval =
      MvPolynomial.eval₂ WeightedSupport.scalarHom
        (fun v => Counting.rowArgument (liftedRow source input (ix.symm v)) (decode p D theta)
          (beta source point input (ix.symm v)) degree) table := by
  let _ : One (Code p D) := ⟨target.one⟩
  have hargument (i : Fin arity) :
      SymbolicCost.denote (SubexpSourceSemantics.decodeRaw (decode p D)
        ((factor source target theta minusOne point input).inputs i)) =
      Counting.rowArgument (liftedRow source input (ix.symm (ix i)))
        (decode p D theta) (beta source point input (ix.symm (ix i))) degree := by
    dsimp only [factor]
    simpa only [Equiv.symm_apply_apply] using
      argument_denote source target theta minusOne point input hminusOne hdegree i
  exact SubexpSourceFactors.factor_value_eq (decode p D) target.one_spec
    (factor source target theta minusOne point input) nodes hu hcache ix table
    (fun v => Counting.rowArgument (liftedRow source input (ix.symm v))
      (decode p D theta) (beta source point input (ix.symm v)) degree) htable hargument

/-- The exact leaf relation consumed by the source-to-jet refinement.
Only the local interpolation cache and source-degree facts are required;
the reference factor's origins, Taylor coefficients, and table are built
from the packet data rather than assumed to have the final factor value. -/
theorem factor_reference
    (hminusOne : wordValue p (D+1) minusOne = -1)
    (hdegree : ∀ i w,
      (((input.sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ degree)
    (nodes : Fin labels → Ring p D) (hu : TableInterpolation.UnitDifferences nodes)
    (hcache : ∀ i : Fin labels,
      PolynomialAlgorithm.denote ((input.cache.map (List.map (decode p D))).getD i.val []) =
        TableInterpolation.basis nodes hu i)
    {r : ℕ} (color : Fin r) :
    FactorReference source target theta minusOne point input color := by
  unfold FactorReference
  let _ : One (Code p D) := ⟨target.one⟩
  let lift := (SubexpActualRing.residueSection p (D+1) (Nat.succ_pos D)).lift
  let data := referenceData source theta input color
  let x := fun w => source.residueRing.decode (point w)
  have harg (i : Fin arity) :
      SubexpProgramBuilder.argumentValue lift data x i =
        Counting.rowArgument (liftedRow source input i) (decode p D theta)
          (beta source point input i) degree := by
    dsimp only [data, referenceData]
    rw [← SubexpProgramBuilder.argument_correct]
    exact SubexpArgumentCode.denote_compileArgument_eq_rowArgument
      (beta source point input i) (decode p D theta)
      (data.taylor i) (liftedRow source input i) (fun _ _ => rfl)
  have htable : data.table = input.rows.map (SubexpRepresentedBuilder.mapRow (decode p D)) := rfl
  have harguments :
      (fun i : Fin arity => SymbolicCost.denote (SubexpSourceSemantics.decodeRaw (decode p D)
        (argument source target theta minusOne point input i))) =
      SubexpProgramBuilder.argumentValue lift data x := by
    funext i
    exact (argument_denote source target theta minusOne point input hminusOne hdegree i).trans
      (harg i).symm
  unfold SubexpSourceReference.FactorRel referenceFactor
  change (((factor source target theta minusOne point input).expression
      (SubexpWeightCode.rawScalar D)).map
        (fun raw => SymbolicCost.denote (SubexpSourceSemantics.decodeRaw (decode p D) raw))).eval =
      ((SubexpProgramBuilder.factorExpr lift (input.cache.map (List.map (decode p D)))
        data x).map SymbolicCost.denote).eval
  rw [SubexpSourceFactors.factor_value (decode p D) target.one_spec
    (factor source target theta minusOne point input) nodes hu hcache,
    SubexpProgramBuilder.factorExpr_correct lift (input.cache.map (List.map (decode p D)))
      nodes hu hcache data x]
  dsimp only [factor]
  unfold SubexpProgramBuilder.factorValue
  rw [htable, harguments]
  rfl

end Value
end

end SubexponentialSAT.SubexpFactorPacketProvenance

end OAI.Algorithms
