import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProgramBuilder

namespace OAI.Algorithms

/-!
# Structural refinement of the represented moment builder

The source coefficient and residue types need only the operations used by the
builder.  Their decoders commute with those operations, but no ring laws are
required on code words.  The conclusions identify the complete generated
expression, rather than assuming its denotation or its final answer.

This module proves representation correctness, not an execution-time bound.
-/

namespace SubexponentialSAT.SubexpRepresentedBuilder

open SubexpProgramBuilder

variable {D p q r : ℕ} {C R CK K F : Type*}

/-- Decode coefficients while preserving every raw exponent index. -/
def mapRaw (decode : C → R) (xs : Raw D C) : Raw D R :=
  xs.map fun x => (x.1, decode x.2)

/-- Labels, including their order and multiplicity, are unchanged. -/
def mapRow (decode : C → R) {k : ℕ}
    (row : SubexpTableInterpolation.Row p k C) : SubexpTableInterpolation.Row p k R :=
  ⟨row.labels, decode row.value⟩

/-- Map only stored residue and lifted-ring coefficients of a factor. -/
def mapFactor (decodeK : CK → K) (decode : C → R)
    (f : FactorData D p q r CK C) : FactorData D p q r K R where
  arity := f.arity
  color := f.color
  origin i w := decodeK (f.origin i w)
  taylor i j w := decode (f.taylor i j w)
  table := f.table.map (mapRow decode)

theorem map_dotList [Zero CK] [Add CK] [Mul CK] [Zero K] [Add K] [Mul K]
    (decode : CK → K) (hzero : decode 0 = 0)
    (hadd : ∀ x y, decode (x + y) = decode x + decode y)
    (hmul : ∀ x y, decode (x * y) = decode x * decode y)
    (row x : Fin D → CK) (coordinates : List (Fin D)) :
    decode (SubexpInputCode.dotListWithCost row x coordinates).1 =
      (SubexpInputCode.dotListWithCost (fun i => decode (row i))
        (fun i => decode (x i)) coordinates).1 := by
  induction coordinates with
  | nil => exact hzero
  | cons i tail ih => simp only [SubexpInputCode.dotListWithCost, hadd, hmul, ih]

theorem map_beta [Zero CK] [Add CK] [Mul CK] [Zero K] [Add K] [Mul K]
    (decodeK : CK → K) (decode : C → R)
    (hzero : decodeK 0 = 0)
    (hadd : ∀ x y, decodeK (x + y) = decodeK x + decodeK y)
    (hmul : ∀ x y, decodeK (x * y) = decodeK x * decodeK y)
    (lift : CK → C) (lift' : K → R)
    (hlift : ∀ x, decode (lift x) = lift' (decodeK x))
    (row x : Fin D → CK) :
    decode (SubexpInputCode.beta lift row x) =
      SubexpInputCode.beta lift' (fun i => decodeK (row i)) (fun i => decodeK (x i)) := by
  simp only [SubexpInputCode.beta, SubexpInputCode.dotWithCost, hlift,
    map_dotList decodeK hzero hadd hmul]

theorem map_power [One C] [Mul C] [One R] [Mul R]
    (decode : C → R) (hone : decode 1 = 1)
    (hmul : ∀ x y, decode (x * y) = decode x * decode y) (x : C) (n : ℕ) :
    decode (SubexpWeightCode.powerWithCost x n).1 =
      (SubexpWeightCode.powerWithCost (decode x) n).1 := by
  induction n with
  | zero => exact hone
  | succ n ih => simp only [SubexpWeightCode.powerWithCost, hmul, ih]

theorem map_weight [One C] [Mul C] [One R] [Mul R]
    (decode : C → R) (hone : decode 1 = 1)
    (hmul : ∀ x y, decode (x * y) = decode x * decode y)
    (x : Fin D → C) (a : Fin D → ℕ) (support : List (Fin D)) :
    decode (SubexpWeightCode.weightWithCost x a support).1 =
      (SubexpWeightCode.weightWithCost (fun i => decode (x i)) a support).1 := by
  induction support with
  | nil => exact hone
  | cons i tail ih =>
      simp only [SubexpWeightCode.weightWithCost, hmul, map_power decode hone hmul, ih]

@[simp] theorem map_rawScalar (decode : C → R) (x : C) :
    mapRaw decode (SubexpWeightCode.rawScalar D x) =
      SubexpWeightCode.rawScalar D (decode x) := rfl

theorem map_rawOne [One C] [One R] (decode : C → R) (hone : decode 1 = 1) :
    mapRaw decode (SubexpAlgorithm.rawOne D) = SubexpAlgorithm.rawOne D := by
  simp only [mapRaw, SubexpAlgorithm.rawOne, List.map_cons, List.map_nil, hone]

theorem map_rawWeight [One C] [Mul C] [One R] [Mul R]
    (decode : C → R) (hone : decode 1 = 1)
    (hmul : ∀ x y, decode (x * y) = decode x * decode y)
    (x : Fin D → C) (a : Fin D → ℕ) (support : List (Fin D)) :
    mapRaw decode (SubexpWeightCode.rawWeightWithCost x a support).1 =
      (SubexpWeightCode.rawWeightWithCost (fun i => decode (x i)) a support).1 := by
  simp only [SubexpWeightCode.rawWeightWithCost, map_rawScalar, map_weight decode hone hmul]

theorem map_compileArgument [Neg C] [Neg R]
    (decode : C → R) (hneg : ∀ x, decode (-x) = -decode x)
    (beta : C) (rows : Fin (q + 1) → Fin D → C) :
    mapRaw decode (SubexpArgumentCode.compileArgument beta rows) =
      SubexpArgumentCode.compileArgument (decode beta) (fun j i => decode (rows j i)) := by
  simp [mapRaw, SubexpArgumentCode.compileArgument, SubexpArgumentCode.rawRow,
    List.map_ofFn, Function.comp_def, hneg]

private theorem map_product {A B : Type*} [One A] [One B]
    (decode : A → B) (hone : decode 1 = 1) (es : List (Algorithm.Expr A)) :
    (Algorithm.Expr.product es).map decode =
      Algorithm.Expr.product (es.map fun e => e.map decode) := by
  induction es with
  | nil => simp only [Algorithm.Expr.product, Algorithm.Expr.map, hone, List.map_nil]
  | cons e es ih => simp only [Algorithm.Expr.product, Algorithm.Expr.map, List.map_cons, ih]

private theorem map_getD {A B : Type*} (f : A → B) (xs : List A) (n : ℕ) (d : A) :
    (xs.map f).getD n (f d) = f (xs.getD n d) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => cases n <;> simp

theorem map_horner (decode : C → R) (x : Algorithm.Expr (Raw D C)) (coeffs : List C) :
    letI : Zero (Raw D C) := ⟨[]⟩
    letI : Zero (Raw D R) := ⟨[]⟩
    (SubexpTableInterpolation.hornerExpr (SubexpWeightCode.rawScalar D) x coeffs).map
        (mapRaw decode) =
      SubexpTableInterpolation.hornerExpr (SubexpWeightCode.rawScalar D)
        (x.map (mapRaw decode)) (coeffs.map decode) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      simp only [SubexpTableInterpolation.hornerExpr, Algorithm.Expr.map,
        map_rawScalar, List.map_cons, ih]

theorem map_rowExpr [One C] [One R] (decode : C → R) (hone : decode 1 = 1)
    (cache : List (List C)) {k : ℕ} (row : SubexpTableInterpolation.Row p k C)
    (inputs : Fin k → Algorithm.Expr (Raw D C)) :
    letI : Zero (Raw D C) := ⟨[]⟩
    letI : One (Raw D C) := ⟨SubexpAlgorithm.rawOne D⟩
    letI : Zero (Raw D R) := ⟨[]⟩
    letI : One (Raw D R) := ⟨SubexpAlgorithm.rawOne D⟩
    (SubexpTableInterpolation.rowExpr (SubexpWeightCode.rawScalar D) cache row inputs).map
        (mapRaw decode) =
      SubexpTableInterpolation.rowExpr (SubexpWeightCode.rawScalar D)
        (cache.map (List.map decode)) (mapRow decode row)
        (fun i => (inputs i).map (mapRaw decode)) := by
  let _ : Zero (Raw D C) := ⟨[]⟩
  let _ : One (Raw D C) := ⟨SubexpAlgorithm.rawOne D⟩
  let _ : Zero (Raw D R) := ⟨[]⟩
  let _ : One (Raw D R) := ⟨SubexpAlgorithm.rawOne D⟩
  simp only [SubexpTableInterpolation.rowExpr, Algorithm.Expr.map, map_rawScalar,
    map_product (mapRaw (D := D) decode) (map_rawOne (D := D) decode hone), List.map_ofFn,
    mapRow]
  congr 3
  funext i
  simp only [Function.comp_apply, map_horner]
  rw [← map_getD (List.map decode) cache (row.labels.get i).val []]
  rfl

theorem map_tableExpr [One C] [One R] (decode : C → R) (hone : decode 1 = 1)
    (cache : List (List C)) {k : ℕ} (rows : List (SubexpTableInterpolation.Row p k C))
    (inputs : Fin k → Algorithm.Expr (Raw D C)) :
    letI : Zero (Raw D C) := ⟨[]⟩
    letI : One (Raw D C) := ⟨SubexpAlgorithm.rawOne D⟩
    letI : Zero (Raw D R) := ⟨[]⟩
    letI : One (Raw D R) := ⟨SubexpAlgorithm.rawOne D⟩
    (SubexpTableInterpolation.tableExpr (SubexpWeightCode.rawScalar D) cache rows inputs).map
        (mapRaw decode) =
      SubexpTableInterpolation.tableExpr (SubexpWeightCode.rawScalar D)
        (cache.map (List.map decode)) (rows.map (mapRow decode))
        (fun i => (inputs i).map (mapRaw decode)) := by
  let _ : Zero (Raw D C) := ⟨[]⟩
  let _ : One (Raw D C) := ⟨SubexpAlgorithm.rawOne D⟩
  let _ : Zero (Raw D R) := ⟨[]⟩
  let _ : One (Raw D R) := ⟨SubexpAlgorithm.rawOne D⟩
  simp only [SubexpTableInterpolation.tableExpr,
    Algorithm.Expr.map_sum (mapRaw (D := D) decode) (by rfl), List.map_map,
    Function.comp_def, map_rowExpr decode hone]

section Builder

variable [Zero CK] [Add CK] [Mul CK] [Zero K] [Add K] [Mul K]
  [One C] [Mul C] [Neg C] [One R] [Mul R] [Neg R]
  (decodeK : CK → K) (decode : C → R)
  (hzero : decodeK 0 = 0)
  (hadd : ∀ x y, decodeK (x + y) = decodeK x + decodeK y)
  (hmul : ∀ x y, decodeK (x * y) = decodeK x * decodeK y)
  (hone : decode 1 = 1)
  (hmulR : ∀ x y, decode (x * y) = decode x * decode y)
  (hneg : ∀ x, decode (-x) = -decode x)
  (betaLift : CK → C) (betaLift' : K → R)
  (hbeta : ∀ x, decode (betaLift x) = betaLift' (decodeK x))

include hzero hadd hmul hneg hbeta

omit [One C] [Mul C] [One R] [Mul R] in
theorem map_argument (f : FactorData D p q r CK C) (x : Fin D → CK)
    (i : Fin f.arity) :
    mapRaw decode (argument betaLift f x i) =
      argument betaLift' (mapFactor decodeK decode f) (fun w => decodeK (x w)) i := by
  unfold argument
  rw [map_compileArgument decode hneg, map_beta decodeK decode hzero hadd hmul
    betaLift betaLift' hbeta]
  rfl

include hone

omit [Mul C] [Mul R] in
theorem map_factorExpr (cache : List (List C)) (f : FactorData D p q r CK C)
    (x : Fin D → CK) :
    (factorExpr betaLift cache f x).map (mapRaw decode) =
      factorExpr betaLift' (cache.map (List.map decode)) (mapFactor decodeK decode f)
        (fun w => decodeK (x w)) := by
  unfold factorExpr
  rw [map_tableExpr decode hone]
  simp only [Algorithm.Expr.map,
    map_argument decodeK decode hzero hadd hmul hneg betaLift betaLift' hbeta]
  rfl

omit [Mul C] [Mul R] in
theorem map_groupExpr (cache : List (List C)) (factors : List (FactorData D p q r CK C))
    (g : Fin r) (x : Fin D → CK) :
    (groupExpr betaLift cache factors g x).map (mapRaw decode) =
      groupExpr betaLift' (cache.map (List.map decode))
        (factors.map (mapFactor decodeK decode)) g (fun w => decodeK (x w)) := by
  let _ : One (Raw D C) := ⟨SubexpAlgorithm.rawOne D⟩
  let _ : One (Raw D R) := ⟨SubexpAlgorithm.rawOne D⟩
  simp only [groupExpr, map_product (mapRaw (D := D) decode) (map_rawOne (D := D) decode hone),
    List.map_map, Function.comp_def,
    map_factorExpr decodeK decode hzero hadd hmul hone hneg betaLift betaLift' hbeta,
    List.filter_map, mapFactor]
  rfl

variable [Add F] (embed : F → CK) (embed' : F → K)
  (hembed : ∀ x, decodeK (embed x) = embed' x)
  (weightLift : F → C) (weightLift' : F → R)
  (hweight : ∀ x, decode (weightLift x) = weightLift' x)

include hmulR hembed hweight

theorem map_block (cache : List (List C)) (factors : List (FactorData D p q r CK C))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    (block embed betaLift weightLift cache factors supports outside base increments a).map
        (mapRaw decode) =
      block embed' betaLift' weightLift' (cache.map (List.map decode))
        (factors.map (mapFactor decodeK decode)) supports outside base increments a := by
  simp only [block, SubexpAlgorithm.Block.ofFibers, SubexpAlgorithm.Block.map,
    Algorithm.WeightedTerm.map, List.map_ofFn, List.map_map, Function.comp_def,
    map_rawWeight decode hone hmulR, hweight,
    map_groupExpr decodeK decode hzero hadd hmul hone hneg betaLift betaLift' hbeta,
    hembed]

theorem map_blocks (cache : List (List C)) (factors : List (FactorData D p q r CK C))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    (blocks embed betaLift weightLift cache factors supports outside bases increments a).map
        (SubexpAlgorithm.Block.map (mapRaw decode)) =
      blocks embed' betaLift' weightLift' (cache.map (List.map decode))
        (factors.map (mapFactor decodeK decode)) supports outside bases increments a := by
  simp only [blocks, List.map_map, Function.comp_def,
    map_block decodeK decode hzero hadd hmul hone hmulR hneg betaLift betaLift' hbeta
      embed embed' hembed weightLift weightLift' hweight]

/-- The complete encoded builder refines the semantic builder structurally.
Only local operation and lift correctness is required; no program/result
equality is an assumption. All enumeration data remain the supplied data. -/
theorem map_rawMomentExpression
    (cache : List (List C)) (factors : List (FactorData D p q r CK C))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    (SubexpAlgorithm.rawMomentExpression
      (blocks embed betaLift weightLift cache factors supports outside bases increments a)).map
        (mapRaw decode) =
      SubexpAlgorithm.rawMomentExpression
        (blocks embed' betaLift' weightLift' (cache.map (List.map decode))
          (factors.map (mapFactor decodeK decode)) supports outside bases increments a) := by
  let _ : Zero (Raw D C) := ⟨[]⟩
  let _ : One (Raw D C) := ⟨SubexpAlgorithm.rawOne D⟩
  let _ : Zero (Raw D R) := ⟨[]⟩
  let _ : One (Raw D R) := ⟨SubexpAlgorithm.rawOne D⟩
  unfold SubexpAlgorithm.rawMomentExpression
  rw [SubexpAlgorithm.map_momentExpression (mapRaw (D := D) decode) (by rfl)
    (map_rawOne (D := D) decode hone)]
  rw [map_blocks decodeK decode hzero hadd hmul hone hmulR hneg betaLift betaLift' hbeta
    embed embed' hembed weightLift weightLift' hweight]

end Builder

/-- Instantiate the structural result with executable operation callbacks.
The only remaining hypotheses concern the three concrete input conversions.
No algebraic laws are required on either code type. -/
theorem represented_rawMomentExpression [CommRing K] [CommRing R] [Add F]
    (kops : SubexpSymbolicCost.RepresentedRing CK K)
    (ops : SubexpSymbolicCost.RepresentedRing C R)
    (embed : F → CK) (embed' : F → K)
    (betaLift : CK → C) (betaLift' : K → R)
    (weightLift : F → C) (weightLift' : F → R)
    (hembed : ∀ x, kops.decode (embed x) = embed' x)
    (hbeta : ∀ x, ops.decode (betaLift x) = betaLift' (kops.decode x))
    (hweight : ∀ x, ops.decode (weightLift x) = weightLift' x)
    (cache : List (List C)) (factors : List (FactorData D p q r CK C))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    letI : Zero CK := ⟨kops.zeroRun.1⟩
    letI : Add CK := ⟨fun x y => (kops.addRun x y).1⟩
    letI : Mul CK := ⟨fun x y => (kops.mulRun x y).1⟩
    letI : One C := ⟨ops.oneRun.1⟩
    letI : Mul C := ⟨fun x y => (ops.mulRun x y).1⟩
    letI : Neg C := ⟨fun x => (ops.negRun x).1⟩
    (SubexpAlgorithm.rawMomentExpression
      (blocks embed betaLift weightLift cache factors supports outside bases increments a)).map
        (SubexpSymbolicCost.decodeList ops) =
      SubexpAlgorithm.rawMomentExpression
        (blocks embed' betaLift' weightLift' (cache.map (List.map ops.decode))
          (factors.map (mapFactor kops.decode ops.decode)) supports outside bases increments a) := by
  let _ : Zero CK := ⟨kops.zeroRun.1⟩
  let _ : Add CK := ⟨fun x y => (kops.addRun x y).1⟩
  let _ : Mul CK := ⟨fun x y => (kops.mulRun x y).1⟩
  let _ : One C := ⟨ops.oneRun.1⟩
  let _ : Mul C := ⟨fun x y => (ops.mulRun x y).1⟩
  let _ : Neg C := ⟨fun x => (ops.negRun x).1⟩
  exact map_rawMomentExpression kops.decode ops.decode kops.zero_correct kops.add_correct
    kops.mul_correct ops.one_correct ops.mul_correct ops.neg_correct betaLift betaLift' hbeta
    embed embed' hembed weightLift weightLift' hweight cache factors supports outside bases increments a

end SubexponentialSAT.SubexpRepresentedBuilder

end OAI.Algorithms
