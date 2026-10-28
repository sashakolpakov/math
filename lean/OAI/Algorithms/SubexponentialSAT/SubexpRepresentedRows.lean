import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorExecution
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse
import OAI.Algorithms.SubexponentialSAT.SubexpExplicitLift
import OAI.Algorithms.SubexponentialSAT.SubexpAnnihilation

namespace OAI.Algorithms

/-!
# Polynomial rows generated from represented field operations

The producer uses code words, finite expression constructors, and the supplied
arithmetic callbacks. It never extracts coefficients from an abstract field
value. Inverse constants are computed by finite-field powering. The canonical
coefficient lift is applied only after compiling the source polynomial.
-/

namespace SubexponentialSAT.SubexpRepresentedRows

open SubexpSymbolicCost SubexpRowInterpolation SubexpTaylorExecution

variable {C E : Type*} {Q : ℕ}

structure NodeCache (C : Type*) (Q : ℕ) where
  node : Fin Q → C
  inverse : Fin Q → C
  difference : Fin Q → Fin Q → C

/-- The same finite inverse algorithm used by the CRT reconstruction. -/
def nodeCache (ops : RingProgram C) (q : ℕ) (node : Fin Q → C) : NodeCache C Q where
  node := node
  inverse i := (SubexpResidueInverse.inverseProgram ops q 1 (node i)).1
  difference i j := (SubexpResidueInverse.differenceInverseProgram ops node q 1 i j).1

def sumCode (zero : C) (ps : List (PolynomialCode C)) : PolynomialCode C :=
  ps.foldr PolynomialCode.add (.constant zero)

def productCode (one : C) (ps : List (PolynomialCode C)) : PolynomialCode C :=
  ps.foldr PolynomialCode.mul (.constant one)

def basis (ops : RingProgram C) (cache : NodeCache C Q)
    (s : Finset (Fin Q)) (i : Fin Q) : PolynomialCode C :=
  .mul (.mul (.constant (cache.inverse i)) .indeterminate)
    (productCode ops.oneRun.1 (List.ofFn fun j : Fin Q =>
      if j ∈ s.erase i then
        .mul (.constant (cache.difference i j))
          (.add .indeterminate (.constant (ops.negRun (cache.node j)).1))
      else .constant ops.oneRun.1))

def correction (ops : RingProgram C) (cache : NodeCache C Q)
    (s : Finset (Fin Q)) (d : Fin Q → C) : PolynomialCode C :=
  sumCode ops.zeroRun.1 (List.ofFn fun i : Fin Q =>
    if i ∈ s then .mul (.constant (d i)) (basis ops cache s i)
    else .constant ops.zeroRun.1)

def row {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (ops : RingProgram C) (cache : NodeCache C Q)
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) : PolynomialCode C :=
  .add (.constant (if v = y then ops.oneRun.1 else ops.zeroRun.1))
    (if y ∈ correctionColumns head σ R then
      correction ops cache (mismatchPositions head σ y) (d y)
    else .constant ops.zeroRun.1)

section Structural

variable [CommRing E] (ops : RepresentedRing C E)

private theorem map_sumCode (ps : List (PolynomialCode C)) :
    mapCode ops.decode (sumCode ops.zeroRun.1 ps) =
      PolynomialCode.sum (ps.map (mapCode ops.decode)) := by
  induction ps with
  | nil => simp [sumCode, PolynomialCode.sum, mapCode, ops.zero_correct]
  | cons p ps ih => simpa only [sumCode, List.foldr_cons, mapCode, List.map_cons,
      PolynomialCode.sum] using congrArg (PolynomialCode.add (mapCode ops.decode p)) ih

private theorem map_productCode (ps : List (PolynomialCode C)) :
    mapCode ops.decode (productCode ops.oneRun.1 ps) =
      PolynomialCode.product (ps.map (mapCode ops.decode)) := by
  induction ps with
  | nil => simp [productCode, PolynomialCode.product, mapCode, ops.one_correct]
  | cons p ps ih => simpa only [productCode, List.foldr_cons, mapCode, List.map_cons,
      PolynomialCode.product] using congrArg (PolynomialCode.mul (mapCode ops.decode p)) ih

variable (cache : NodeCache C Q) {node : Fin Q → E} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hinv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)

include hnode hinv hdiff in
theorem map_basis (s : Finset (Fin Q)) (i : Fin Q) :
    mapCode ops.decode (basis ops.program cache s i) = basisCode units s i := by
  simp only [basis, basisCode, mapCode, hinv, map_productCode, List.map_ofFn]
  congr 2
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply]
  split_ifs <;> simp [mapCode, ops.neg_correct, hnode, hdiff, ops.one_correct]

include hnode hinv hdiff in
theorem map_correction (s : Finset (Fin Q)) (d : Fin Q → C) :
    mapCode ops.decode (correction ops.program cache s d) =
      correctionCode units s (fun i => ops.decode (d i)) := by
  simp only [correction, RepresentedRing.program, map_sumCode, correctionCode, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  split_ifs
  · change (PolynomialCode.constant (ops.decode (d i))).mul
      (mapCode ops.decode (basis ops.program cache s i)) = _
    rw [map_basis ops cache units hnode hinv hdiff]
  · simp only [mapCode, ops.zero_correct]

include hnode hinv hdiff in
theorem map_row {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) :
    mapCode ops.decode (row ops.program cache v head σ R d y) =
      mismatchRowCode v head σ R units (fun y i => ops.decode (d y i)) y := by
  simp only [row, mapCode, mismatchRowCode, RepresentedRing.program]
  congr 1
  · split_ifs with h
    · subst y; simp [ops.one_correct]
    · simp [h, ops.zero_correct]
  · by_cases hy : y ∈ correctionColumns head σ R
    · simp only [ite_eq_left hy]
      exact map_correction ops cache units hnode hinv hdiff _ _
    · simp only [ite_eq_right hy, mapCode, ops.zero_correct]

end Structural

section ComputedInverses

variable [Field E] [Fintype E] (ops : RepresentedRing C E)
variable (q : ℕ) (hq : Fintype.card E = q) (node : Fin Q → C)
variable (hinj : Function.Injective (fun i => ops.decode (node i)))
variable (hne : ∀ i, ops.decode (node i) ≠ 0)

include hq in
private theorem inverseProgram_mul (a : C) (ha : ops.decode a ≠ 0) :
    ops.decode (SubexpResidueInverse.inverseProgram ops.program q 1 a).1 *
      ops.decode a = 1 := by
  rw [SubexpResidueInverse.inverseProgram_run]
  exact SubexpResidueInverse.inverseRun_correct ops (RingHom.id E) q hq 0 1
    (by simp) (by intro x hx; simpa using hx) a ha

include hq hne in
theorem nodeCache_inverse (units : NodeUnits (fun i => ops.decode (node i))) (i : Fin Q) :
    ops.decode ((nodeCache ops.program q node).inverse i) = units.nodeInverse i := by
  apply mul_right_cancel₀ (hne i)
  rw [units.nodeInverse_mul]
  exact inverseProgram_mul ops q hq (node i) (hne i)

include hq hinj in
theorem nodeCache_difference (units : NodeUnits (fun i => ops.decode (node i)))
    (i j : Fin Q) :
    ops.decode ((nodeCache ops.program q node).difference i j) =
      units.differenceInverse i j := by
  by_cases hij : i = j
  · subst j
    simp [nodeCache, SubexpResidueInverse.differenceInverseProgram,
      NodeUnits.differenceInverse, RepresentedRing.program, ops.zero_correct]
  · have hn : ops.decode (node i) - ops.decode (node j) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hij (hinj h))
    apply mul_right_cancel₀ hn
    rw [units.differenceInverse_mul hij]
    change ops.decode (SubexpResidueInverse.differenceInverseProgram ops.program node q 1 i j).1 * _ = 1
    simp only [SubexpResidueInverse.differenceInverseProgram, ite_eq_right hij]
    have ha : ops.decode (ops.addRun (node i) (ops.negRun (node j)).1).1 ≠ 0 := by
      simpa only [ops.add_correct, ops.neg_correct, ← sub_eq_add_neg] using hn
    simpa only [ops.add_correct, ops.neg_correct, ← sub_eq_add_neg] using
      inverseProgram_mul ops q hq (ops.addRun (node i) (ops.negRun (node j)).1).1 ha

include hq hinj hne in
theorem computed_row_decode {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V)
    (units : NodeUnits (fun i => ops.decode (node i))) :
    (mapCode ops.decode (row ops.program (nodeCache ops.program q node) v head σ R d y)).denote =
      mismatchRowPath v head σ R units (fun y i => ops.decode (d y i)) y := by
  rw [map_row ops _ units (fun _ => rfl)
    (nodeCache_inverse ops q hq node hne units)
    (nodeCache_difference ops q hq node hinj units)]
  exact mismatchRowCode_denote _ _ _ _ _ _ _

end ComputedInverses

section MatrixRows

open MulticolorTypes

variable {K : Type*} [Ring K] {r Δ : ℕ}

/-- Zero extension is performed in the finite prime-field matrix before its
entry is embedded as a coefficient word. -/
def matrixValues (ops : RingProgram C) (embed : K → C)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) K)
    (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) : C :=
  (ops.negRun (embed (SubexpAnnihilation.zeroExtendMatrix
    (joint t (y.head t) i) (M t (y.head t) i) u y))).1

def matrixRow (ops : RingProgram C) (cache : NodeCache C Q) (embed : K → C)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) K)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (y : UniversalType r Q Δ) : PolynomialCode C :=
  row ops cache u (fun y => y.head) (u.slot i) R (matrixValues ops embed M u i) y

variable [CommRing E] (ops : RepresentedRing C E) (cache : NodeCache C Q)
variable {node : Fin Q → E} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hinv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)

include hnode hinv hdiff in
theorem matrixRow_decode (embed : K → C) (φ : K →+* E)
    (hembed : ∀ a, ops.decode (embed a) = φ a)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) K)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (y : UniversalType r Q Δ) :
    (mapCode ops.decode (matrixRow ops.program cache embed M u i R y)).denote =
      SubexpAnnihilation.rowForMatrices φ M u i R units y := by
  unfold matrixRow
  rw [map_row ops cache units hnode hinv hdiff, mismatchRowCode_denote]
  congr 2
  funext z t
  simp only [matrixValues, ops.neg_correct, hembed,
    SubexpAnnihilation.matrixPrescription]

end MatrixRows

section CoefficientLift

variable {A Λ : Type*}

/-- A monomial expression with a represented multiplicative identity. -/
def powerX (one : C) : ℕ → PolynomialCode C
  | 0 => .constant one
  | n + 1 => .mul .indeterminate (powerX one n)

/-- Compile the source expression first, then lift exactly the requested
coefficient range. A residue section need not preserve sums or products. -/
def liftCode (source : RingProgram C) (target : RingProgram A)
    (lift : C → A) (bound : ℕ) (P : PolynomialCode C) : PolynomialCode A :=
  let dense := (compileCodeProgram source P).1
  sumCode target.zeroRun.1 (List.ofFn fun i : Fin (bound + 1) =>
    .mul (.constant (lift (readProgram source.zeroRun.1 dense i.val).1))
      (powerX target.oneRun.1 i.val))

/-- The origin vector is evaluated in the source field, using the same
compiled coefficients as the lifted polynomial producer. -/
def originValue (source : RingProgram C) (P : PolynomialCode C) (node : C) : C :=
  (SubexpDensePolynomial.evalProgram source node (compileCodeProgram source P).1).1

variable [CommRing E] [CommRing Λ]
variable (source : RepresentedRing C E) (target : RepresentedRing A Λ)

private theorem powerX_decode (n : ℕ) :
    (mapCode target.decode (powerX target.oneRun.1 n)).denote = Polynomial.X ^ n := by
  induction n with
  | zero => simp [powerX, mapCode, PolynomialCode.denote, target.one_correct]
  | succ n ih => simp [powerX, mapCode, PolynomialCode.denote, ih, pow_succ']

theorem liftCode_decode (lift : C → A) (sectionValue : E → Λ)
    (hlift : ∀ x, target.decode (lift x) = sectionValue (source.decode x))
    (bound : ℕ) (P : PolynomialCode C) :
    (mapCode target.decode (liftCode source.program target.program lift bound P)).denote =
      SubexpExplicitLift.liftPolynomial sectionValue bound (mapCode source.decode P).denote := by
  unfold liftCode
  rw [show target.program.zeroRun.1 = target.zeroRun.1 from rfl, map_sumCode]
  simp only [PolynomialCode.denote_sum, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, mapCode, PolynomialCode.denote, hlift]
  rw [SubexpExplicitLift.liftPolynomial_eq_coefficientData]
  apply Finset.sum_congr rfl
  intro i _
  rw [show source.program.zeroRun.1 = source.zeroRun.1 from rfl,
    readProgram_coeff source _ source.zero_correct, compileCodeProgram_denote,
    show target.program.oneRun.1 = target.oneRun.1 from rfl, powerX_decode]
  simp only [SubexpExplicitLift.coefficientData, Polynomial.C_mul_X_pow_eq_monomial]

theorem originValue_decode (P : PolynomialCode C) (node : C) :
    source.decode (originValue source.program P node) =
      (mapCode source.decode P).denote.eval (source.decode node) := by
  unfold originValue
  rw [SubexpDensePolynomial.evalProgram_run, SubexpDensePolynomial.evalRun_correct,
    PolynomialAlgorithm.eval_eq, compileCodeProgram_denote]

end CoefficientLift

end SubexponentialSAT.SubexpRepresentedRows

end OAI.Algorithms
