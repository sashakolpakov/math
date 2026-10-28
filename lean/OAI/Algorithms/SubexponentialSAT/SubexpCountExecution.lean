import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProgramCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpJetExecution
import OAI.Algorithms.SubexponentialSAT.SubexpRepresentedBuilder
import OAI.Algorithms.SubexponentialSAT.SubexpCRTExecution
import OAI.Algorithms.SubexponentialSAT.SubexpTableExecution

namespace OAI.Algorithms

/-!
# From generated multicolor programs to the actual global polynomial

This module closes the gap between the explicit enumeration used by the
program builder and the coset-based counting proof.  It derives the true jet
from the local factor data; equality to a jet or to the final count is never
an input to that derivation.  Represented CRT integration is added below.
-/

namespace SubexponentialSAT.SubexpCountExecution

open scoped BigOperators
open SubexpLayoutSpec

private theorem coeff_eq_getD {R : Type*} [Semiring R] (P : List R) (n : ℕ) :
    PolynomialAlgorithm.coeff P n = P.getD n 0 := by
  induction P generalizing n with
  | nil => rfl
  | cons a P ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

/-- A low-degree-first coefficient array denotes exactly the requested
polynomial truncation, including trailing zero coefficients. -/
theorem denote_coefficientList {R : Type*} [CommSemiring R] (D : ℕ) (f : Polynomial R) :
    PolynomialAlgorithm.denote ((List.range D).map f.coeff) = Truncation.trunc D f := by
  ext n
  rw [PolynomialAlgorithm.coeff_denote, coeff_eq_getD, Truncation.coeff_trunc]
  by_cases hn : n < D
  · simp [List.getD, hn]
  · have hlen : ((List.range D).map f.coeff).length ≤ n := by simpa using Nat.le_of_not_gt hn
    rw [List.getD_eq_default _ _ hlen, ite_eq_right hn]

theorem denote_jetCoefficientList {R : Type*} [CommRing R]
    (D : ℕ) (θ : R) (H : Polynomial R) :
    PolynomialAlgorithm.denote ((List.range D).map (JetCRT.jet θ D H).coeff) =
      JetCRT.jet θ D H := by
  rw [denote_coefficientList, Counting.jet_eq_trunc]
  exact TruncatedInverse.trunc_idempotent D _

section EnumeratedJets

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F K R : Type*} [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] {P : Factor.Pattern (Fin D) F}
  {c : Parameters p k Δ r tau} {L : Layout (E := K) P c}

/-- The moment calculation indexed by the actual basepoint/increment arrays
supplied to the finite program. -/
noncomputable def enumeratedJet (A : LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (t : Fin c.Q) (enum : EnumerationData L t) : Polynomial R :=
  SubexpCounting.separatedJet (D + 1) D
    (SubexpComputedWeights.enumerationFiberEquiv enum)
    (fun _ g => enum.zeroIndex g)
    (SubexpCounting.layoutGroup A lift hLift sectionLift table t)
    (fun a o => SubexpComputedWeights.outsideValue
      (SubexpEnumerationCode.supportLists L t) lift (enum.outerBase o) a)
    (fun a o g y => SubexpComputedWeights.insideValue
      (SubexpEnumerationCode.supportLists L t) lift
        (enum.outerBase o) (enum.increment g y) a g)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- All enumeration-specific semantic premises are discharged, including
the finite coefficient support and the vanishing of high U powers. -/
theorem enumeratedJet_eq (A : LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hnil : (p : R) ^ (D + 1) = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (t : Fin c.Q) (enum : EnumerationData L t) :
    enumeratedJet A lift hLift sectionLift table t enum =
      JetCRT.jet (A.theta t) D (GlobalPolynomial.rowGlobalPolynomial table A.row lift) := by
  classical
  calc
    enumeratedJet A lift hLift sectionLift table t enum =
        ∑ x : Fin D → ZMod p, Truncation.trunc D
          (Truncation.evalXU (fun w => lift (x w))
            (∏ g, SubexpCounting.layoutGroup A lift hLift sectionLift table t g x)) := by
      unfold enumeratedJet
      refine SubexpCounting.separatedJet_eq_sum
        (ι := Fin D) (Ω := Fin D → ZMod p) (O := Fin enum.outerCount)
        (G := Fin r) (X := fun _ g => Fin (enum.innerCount g)) (R := R)
        (D + 1) D (SubexpComputedWeights.enumerationFiberEquiv enum)
        (fun _ g => enum.zeroIndex g)
        (SubexpCounting.layoutGroup A lift hLift sectionLift table t)
        (fun x w => lift (x w))
        (fun a o => SubexpComputedWeights.outsideValue
          (SubexpEnumerationCode.supportLists L t) lift (enum.outerBase o) a)
        (fun a o g y => SubexpComputedWeights.insideValue
          (SubexpEnumerationCode.supportLists L t) lift
            (enum.outerBase o) (enum.increment g y) a g) ?_ ?_ ?_ ?_
      · exact SubexpProgramCorrectness.layoutGroup_enumeration_invariant
          A lift hLift sectionLift table t enum
      · exact SubexpComputedWeights.enumeration_kernel_weight_split enum
          (SubexpEnumerationCode.supportLists L t)
          (SubexpEnumerationCode.supportLists_nodup L t)
          (SubexpEnumerationCode.supportLists_toFinset L t) lift
      · intro g x
        exact Counting.rowGroup_admissible _ table A.row (A.theta t) c.R _ x
      · intro x j hj
        exact SubexpGlobalPolynomial.colored_rowGroup_highU
          (fun e => L.color e t) table A.row (A.theta t) c.R
          (SubexpCounting.layoutBeta A lift hLift sectionLift t)
          x (fun w => lift (x w)) (p : R) (D + 1) hnil
          (fun e i => SubexpCounting.layoutBeta_defect A lift hLift sectionLift hker t x e i)
          j hj
    _ = _ := by
      rw [Counting.jet_eq_trunc]
      exact SubexpGlobalPolynomial.sum_trunc_evalXU_colored_rowGroups D
        (fun e => L.color e t) table A.row (A.theta t) c.R
        (SubexpCounting.layoutBeta A lift hLift sectionLift t)
        (fun x w => lift (x w)) A.row_degree

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The program on actual finite factor records returns the coefficients of
the global jet. All hypotheses describe individual table/row entries. -/
theorem executeProgram_eq_jet
    (A : LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (cache : List (List R)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (data : F → SubexpProgramBuilder.FactorData D p c.R r K R)
    (ix : ∀ e, Fin (data e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (data e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (data e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (data e).origin i w = (L.row e (ix e i) w).eval (L.node t))
    (htaylor : ∀ e i j w, (data e).taylor i j w =
      ((A.row e (ix e i) w).comp (Polynomial.X + Polynomial.C (A.theta t))).coeff j.val)
    (hnil : (p : R) ^ (D + 1) = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R)) :
    SubexpEnumerationCode.executeProgram enum (algebraMap (ZMod p) K) sectionLift.lift
      lift cache (es.map data) =
      (List.range D).map fun j =>
        (JetCRT.jet (A.theta t) D
          (GlobalPolynomial.rowGlobalPolynomial table A.row lift)).coeff j := by
  rw [SubexpProgramCorrectness.executeProgram_eq_separatedJet
    A lift hLift sectionLift t enum cache labels hu hcache es hnodup hcomplete
    data ix table hcolor htable horigin htaylor]
  change (List.range D).map (fun j =>
    (enumeratedJet A lift hLift sectionLift table t enum).coeff j) = _
  rw [enumeratedJet_eq A lift hLift sectionLift table hnil hker]

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The generated program returns the coefficients of the actual global
jet. Taylor arrays are computed from finite row syntax by `buildFactors`. -/
theorem executeBuiltFactors_eq_jet
    (A : LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (cache : List (List R)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (source : F → SubexpFactorCode.FactorSource D p r K R)
    (ix : ∀ e, Fin (source e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (source e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (source e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (source e).origin i w = (L.row e (ix e i) w).eval (L.node t))
    (hrow : ∀ e i w, ((source e).rows i w).denote = A.row e (ix e i) w)
    (hnil : (p : R) ^ (D + 1) = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R)) :
    SubexpEnumerationCode.executeProgram enum (algebraMap (ZMod p) K) sectionLift.lift
      lift cache (SubexpFactorCode.buildFactors (A.theta t) c.R (es.map source)).data =
      (List.range D).map fun j =>
        (JetCRT.jet (A.theta t) D
          (GlobalPolynomial.rowGlobalPolynomial table A.row lift)).coeff j := by
  rw [SubexpProgramCorrectness.executeBuiltFactors_eq_separatedJet
    A lift hLift sectionLift t enum cache labels hu hcache es hnodup hcomplete
    source ix table hcolor htable horigin hrow]
  change (List.range D).map (fun j =>
    (enumeratedJet A lift hLift sectionLift table t enum).coeff j) = _
  rw [enumeratedJet_eq A lift hLift sectionLift table hnil hker]

end EnumeratedJets

section RepresentedPrograms

variable {D p q r : ℕ} {B CK C : Type*} [Add B]

/-- Build and execute every retained moment using only the supplied ring
callbacks. No polynomial decoder or mathematical jet occurs in this code. -/
def representedJet
    (kprog : SubexpSymbolicCost.RingProgram CK)
    (prog : SubexpSymbolicCost.RingProgram C)
    (embed : B → CK) (betaLift : CK → C) (weightLift : B → C)
    (cache : List (List C))
    (factors : List (SubexpProgramBuilder.FactorData D p q r CK C))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → B)) (increments : Fin r → List (Fin D → B)) :
    List C × ℕ := by
  letI : Zero CK := ⟨kprog.zeroRun.1⟩
  letI : Add CK := ⟨fun x y => (kprog.addRun x y).1⟩
  letI : Mul CK := ⟨fun x y => (kprog.mulRun x y).1⟩
  letI : One C := ⟨prog.oneRun.1⟩
  letI : Mul C := ⟨fun x y => (prog.mulRun x y).1⟩
  letI : Neg C := ⟨fun x => (prog.negRun x).1⟩
  exact SubexpJetExecution.executeJet prog (fun a =>
    SubexpAlgorithm.rawMomentExpression (SubexpProgramBuilder.blocks embed betaLift
      weightLift cache factors supports outside bases increments a))

@[simp] theorem representedJet_length
    (kprog : SubexpSymbolicCost.RingProgram CK)
    (prog : SubexpSymbolicCost.RingProgram C)
    (embed : B → CK) (betaLift : CK → C) (weightLift : B → C)
    (cache : List (List C))
    (factors : List (SubexpProgramBuilder.FactorData D p q r CK C))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → B)) (increments : Fin r → List (Fin D → B)) :
    (representedJet kprog prog embed betaLift weightLift cache factors
      supports outside bases increments).1.length = D :=
  SubexpJetExecution.executeJet_length _ _

variable {K R : Type*} [CommRing K] [CommRing R]

/-- Structural builder refinement and the actual coefficient interpreter
compose. Only local input-conversion laws remain; no program or answer
equality is supplied by the caller. -/
theorem representedJet_decode
    (kops : SubexpSymbolicCost.RepresentedRing CK K)
    (ops : SubexpSymbolicCost.RepresentedRing C R)
    (embed : B → CK) (embed' : B → K)
    (betaLift : CK → C) (betaLift' : K → R)
    (weightLift : B → C) (weightLift' : B → R)
    (hembed : ∀ x, kops.decode (embed x) = embed' x)
    (hbeta : ∀ x, ops.decode (betaLift x) = betaLift' (kops.decode x))
    (hweight : ∀ x, ops.decode (weightLift x) = weightLift' x)
    (cache : List (List C))
    (factors : List (SubexpProgramBuilder.FactorData D p q r CK C))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → B)) (increments : Fin r → List (Fin D → B)) :
    (representedJet kops.program ops.program embed betaLift weightLift cache factors
      supports outside bases increments).1.map ops.decode =
      SubexpProgramBuilder.executeJet embed' betaLift' weightLift'
        (cache.map (List.map ops.decode))
        (factors.map (SubexpRepresentedBuilder.mapFactor kops.decode ops.decode))
        supports outside bases increments := by
  let _ : Zero CK := ⟨kops.zeroRun.1⟩
  let _ : Add CK := ⟨fun x y => (kops.addRun x y).1⟩
  let _ : Mul CK := ⟨fun x y => (kops.mulRun x y).1⟩
  let _ : One C := ⟨ops.oneRun.1⟩
  let _ : Mul C := ⟨fun x y => (ops.mulRun x y).1⟩
  let _ : Neg C := ⟨fun x => (ops.negRun x).1⟩
  unfold representedJet
  rw [SubexpJetExecution.executeJet_decode]
  unfold SubexpProgramBuilder.executeJet SubexpAlgorithm.executeJet
  congr 1
  funext a
  exact SubexpRepresentedBuilder.represented_rawMomentExpression kops ops
    embed embed' betaLift betaLift' weightLift weightLift' hembed hbeta hweight
    cache factors supports outside bases increments a

end RepresentedPrograms

section Pipeline

variable {D p q r Q : ℕ} {B CK C : Type*} [Add B]

/-- Compute each code-word jet once, cache it, and run the full represented
CRT including inverse preprocessing. Counters include all jet-interpreter
and CRT callbacks; expression-building costs are accounted for separately. -/
def countPolynomial
    (kprog : SubexpSymbolicCost.RingProgram CK)
    (prog : SubexpSymbolicCost.RingProgram C)
    (θ : Fin Q → C) (fieldCard : ℕ)
    (embed : B → CK) (betaLift : CK → C) (weightLift : B → C)
    (cache : List (List C))
    (factors : Fin Q → List (SubexpProgramBuilder.FactorData D p q r CK C))
    (supports : Fin Q → Fin r → List (Fin D))
    (outside : Fin Q → List (Fin D))
    (bases : Fin Q → List (Fin D → B))
    (increments : Fin Q → Fin r → List (Fin D → B)) : List C × ℕ :=
  let jets := List.Vector.ofFn (fun t => representedJet kprog prog embed betaLift weightLift
    cache (factors t) (supports t) (outside t) (bases t) (increments t))
  let result := SubexpCRTExecution.completeProgram prog θ fieldCard (D + 1) D
    (fun t => (jets.get t).1)
  (result.1, (jets.toList.map Prod.snd).sum + result.2)

end Pipeline

section RepresentedLayout

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F K R CK C : Type*} [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] {P : Factor.Pattern (Fin D) F}
  {c : Parameters p k Δ r tau} {L : Layout (E := K) P c}

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The executed code-word jet is the true global jet. Every program
refinement is derived structurally; the assumptions concern only scalar
conversions and individual stored input entries. -/
theorem representedJet_eq_jet
    (A : LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (kops : SubexpSymbolicCost.RepresentedRing CK K)
    (ops : SubexpSymbolicCost.RepresentedRing C R)
    (embed : ZMod p → CK) (betaLift : CK → C) (weightLift : ZMod p → C)
    (hembed : ∀ z, kops.decode (embed z) = algebraMap (ZMod p) K z)
    (hbeta : ∀ x, ops.decode (betaLift x) = sectionLift.lift (kops.decode x))
    (hweight : ∀ z, ops.decode (weightLift z) = lift z)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (cache : List (List C)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote ((cache.map (List.map ops.decode)).getD i.val []) =
        TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (data : F → SubexpProgramBuilder.FactorData D p c.R r CK C)
    (ix : ∀ e, Fin (data e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (data e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu
      (SubexpRepresentedBuilder.mapFactor kops.decode ops.decode (data e)).table =
        MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, kops.decode ((data e).origin i w) =
      (L.row e (ix e i) w).eval (L.node t))
    (htaylor : ∀ e i j w, ops.decode ((data e).taylor i j w) =
      ((A.row e (ix e i) w).comp (Polynomial.X + Polynomial.C (A.theta t))).coeff j.val)
    (hnil : (p : R) ^ (D + 1) = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R)) :
    (representedJet kops.program ops.program embed betaLift weightLift cache (es.map data)
      (SubexpEnumerationCode.supportLists L t) (SubexpEnumerationCode.outsideList L t)
      (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum)).1.map
        ops.decode =
      (List.range D).map fun j => (JetCRT.jet (A.theta t) D
        (GlobalPolynomial.rowGlobalPolynomial table A.row lift)).coeff j := by
  rw [representedJet_decode kops ops embed (algebraMap (ZMod p) K)
    betaLift sectionLift.lift weightLift lift hembed hbeta hweight]
  have h := executeProgram_eq_jet A lift hLift sectionLift t enum
    (cache.map (List.map ops.decode)) labels hu hcache es hnodup hcomplete
    (fun e => SubexpRepresentedBuilder.mapFactor kops.decode ops.decode (data e))
    ix table hcolor htable horigin htaylor hnil hker
  unfold SubexpEnumerationCode.executeProgram SubexpEnumerationCode.programBlocks at h
  simpa only [List.map_map, Function.comp_def, SubexpProgramBuilder.executeJet] using h

omit [FiniteDimensional (ZMod p) K] in
/-- Full represented reconstruction from the actual factor records. The
jet and final polynomial equalities are derived, not supplied as premises. -/
theorem countPolynomial_eq
    (A : LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (kops : SubexpSymbolicCost.RepresentedRing CK K)
    (ops : SubexpSymbolicCost.RepresentedRing C R)
    (θ : Fin c.Q → C) (hnode : ∀ t, ops.decode (θ t) = A.theta t)
    (fieldCard : ℕ) (hfield : Fintype.card K = fieldCard)
    (embed : ZMod p → CK) (betaLift : CK → C) (weightLift : ZMod p → C)
    (hembed : ∀ z, kops.decode (embed z) = algebraMap (ZMod p) K z)
    (hbeta : ∀ x, ops.decode (betaLift x) = sectionLift.lift (kops.decode x))
    (hweight : ∀ z, ops.decode (weightLift z) = lift z)
    (enum : ∀ t, EnumerationData L t)
    (cache : List (List C)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote ((cache.map (List.map ops.decode)).getD i.val []) =
        TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (data : Fin c.Q → F → SubexpProgramBuilder.FactorData D p c.R r CK C)
    (ix : ∀ t e, Fin (data t e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ t e, (data t e).color = L.color e t)
    (htable : ∀ t e, SubexpTableInterpolation.tablePolynomial labels hu
      (SubexpRepresentedBuilder.mapFactor kops.decode ops.decode (data t e)).table =
        MvPolynomial.rename (ix t e).symm (table e))
    (horigin : ∀ t e i w, kops.decode ((data t e).origin i w) =
      (L.row e (ix t e i) w).eval (L.node t))
    (htaylor : ∀ t e i j w, ops.decode ((data t e).taylor i j w) =
      ((A.row e (ix t e i) w).comp (Polynomial.X + Polynomial.C (A.theta t))).coeff j.val)
    (hnil : (p : R) ^ (D + 1) = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (hD : 0 < D)
    (hdegree : (GlobalPolynomial.rowGlobalPolynomial table A.row lift).natDegree < c.Q * D) :
    PolynomialAlgorithm.denote
      ((countPolynomial kops.program ops.program θ fieldCard embed betaLift weightLift cache
        (fun t => es.map (data t))
        (SubexpEnumerationCode.supportLists L) (SubexpEnumerationCode.outsideList L)
        (fun t => SubexpEnumerationCode.outerBases (enum t))
        (fun t => SubexpEnumerationCode.innerIncrements (enum t))).1.map ops.decode) =
      GlobalPolynomial.rowGlobalPolynomial table A.row lift := by
  let _ : NeZero c.Q := ⟨Nat.ne_of_gt c.toConstants.Q_pos⟩
  simp only [countPolynomial, List.Vector.get_ofFn]
  apply SubexpCRTExecution.completeProgram_correct ops θ A.residue fieldCard hfield
    (p : R) (D + 1) hnil
  · intro x hx
    rw [← Ideal.mem_span_singleton, ← hker]
    exact hx
  · intro i j hij
    apply L.node_injective
    simpa only [hnode, A.residue_theta] using hij
  · exact hD
  · exact hdegree
  · intro t
    change Truncation.trunc D (PolynomialAlgorithm.denote
      ((representedJet kops.program ops.program embed betaLift weightLift cache
        (es.map (data t)) (SubexpEnumerationCode.supportLists L t)
        (SubexpEnumerationCode.outsideList L t) (SubexpEnumerationCode.outerBases (enum t))
        (SubexpEnumerationCode.innerIncrements (enum t))).1.map ops.decode)) = _
    rw [representedJet_eq_jet A lift hLift sectionLift kops ops embed betaLift weightLift
      hembed hbeta hweight t (enum t) cache labels hu hcache es hnodup hcomplete
      (data t) (ix t) table (hcolor t) (htable t) (horigin t) (htaylor t) hnil hker,
      denote_jetCoefficientList, hnode, Counting.jet_eq_trunc]
    exact TruncatedInverse.trunc_idempotent D _
  · intro t
    exact (representedJet_length _ _ _ _ _ _ _ _ _ _ _).le

end RepresentedLayout

section SelectedRing

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F CK C : Type*} [Fintype F] [DecidableEq F]
  (S : Factor.System (Fin D) F (ZMod p))
  {c : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) S.toPattern c)
  (kops : SubexpSymbolicCost.RepresentedRing CK (SubexpActualRing.E p))
  (ops : SubexpSymbolicCost.RepresentedRing C (SubexpActualRing.Ring p (D + 1)))

local notation "Λ" => SubexpActualRing.Ring p (D + 1)
local notation "A" => SubexpCounting.selectedLiftedLayout S L (D + 1) (Nat.succ_pos D)
local notation "coord" => SubexpActualRing.coordinateLift p (D + 1)
local notation "coordUnits" => SubexpActualRing.coordinateLift_unitDifferences p (D + 1)
local notation "sectionLift" => SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)
local notation "baseMap" => LiftRing.of (SubexpActualRing.F p (D + 1))
local notation "labels" =>
  (fun i : Fin p => ops.decode (List.Vector.get
    (Prod.fst (SubexpTableExecution.labelsProgram ops.program p)) i))
local notation "labelUnits" => SubexpTableExecution.encodedIntegerUnits ops (D + 1)
  (Fact.out : p.Prime) baseMap _ (SubexpTableExecution.labelsProgram_correct ops p)

/-- Concrete finite data, with only local representation certificates.
No field asks for a correct group, moment, jet, polynomial, or count. -/
structure SelectedInput where
  node : Fin c.Q → C
  node_decode : ∀ t, ops.decode (node t) = (A).theta t
  embed : ZMod p → CK
  embed_decode : ∀ z, kops.decode (embed z) = algebraMap (ZMod p) (SubexpActualRing.E p) z
  betaLift : CK → C
  beta_decode : ∀ x, ops.decode (betaLift x) = (sectionLift).lift (kops.decode x)
  weightLift : ZMod p → C
  weight_decode : ∀ z, ops.decode (weightLift z) = coord z
  enumeration : ∀ t, EnumerationData L t
  supports : Fin c.Q → Fin r → List (Fin D)
  supports_eq : supports = SubexpEnumerationCode.supportLists L
  outside : Fin c.Q → List (Fin D)
  outside_eq : outside = SubexpEnumerationCode.outsideList L
  bases : Fin c.Q → List (Fin D → ZMod p)
  bases_eq : bases = fun t => SubexpEnumerationCode.outerBases (enumeration t)
  increments : Fin c.Q → Fin r → List (Fin D → ZMod p)
  increments_eq : increments = fun t => SubexpEnumerationCode.innerIncrements (enumeration t)
  factors : List F
  factors_nodup : factors.Nodup
  factors_complete : ∀ e, e ∈ factors
  data : Fin c.Q → F → SubexpProgramBuilder.FactorData D p c.R r CK C
  scopeIndex : ∀ t e, Fin (data t e).arity ≃ {v // v ∈ S.scope e}
  color_eq : ∀ t e, (data t e).color = L.color e t
  table_eq : ∀ t e, SubexpTableInterpolation.tablePolynomial labels labelUnits
    (SubexpRepresentedBuilder.mapFactor kops.decode ops.decode (data t e)).table =
      MvPolynomial.rename (scopeIndex t e).symm
        (GlobalPolynomial.interpolatedTable S coord coordUnits e)
  origin_eq : ∀ t e i w, kops.decode ((data t e).origin i w) =
    (L.row e (scopeIndex t e i) w).eval (L.node t)
  taylor_eq : ∀ t e i j w, ops.decode ((data t e).taylor i j w) =
    (((A).row e (scopeIndex t e i) w).comp (Polynomial.X + Polynomial.C ((A).theta t))).coeff j.val

/-- The composed coefficient routine. Table bases, jets, and all CRT
inverses are computed internally; the input supplies the finite source data.
The underlying runtime functions take only executable operation callbacks. -/
noncomputable def runSelected (input : SelectedInput S L kops ops) : List C × ℕ :=
  let cache := SubexpTableExecution.completeProgram ops.program p (D + 1)
  let result := countPolynomial kops.program ops.program input.node (p ^ 4)
    input.embed input.betaLift input.weightLift cache.1
    (fun t => input.factors.map (input.data t))
    input.supports input.outside input.bases input.increments
  (result.1, cache.2 + result.2)

/-- Executed represented coefficients reconstruct the actual global
polynomial. All field, ring, interpolation, and degree premises are derived. -/
theorem runSelected_denote (input : SelectedInput S L kops ops) (hD : 0 < D) :
    PolynomialAlgorithm.denote ((runSelected S L kops ops input).1.map ops.decode) =
      GlobalPolynomial.interpolatedGlobalPolynomial S coord coordUnits (A).row := by
  simp only [runSelected, input.supports_eq, input.outside_eq,
    input.bases_eq, input.increments_eq]
  apply countPolynomial_eq A coord
    (SubexpActualRing.rho_coordinateLift p (D + 1) (Nat.succ_pos D)) sectionLift
    kops ops input.node input.node_decode (p ^ 4) (SubexpActualRing.extension_card p)
    input.embed input.betaLift input.weightLift
    input.embed_decode input.beta_decode input.weight_decode input.enumeration
    (SubexpTableExecution.completeProgram ops.program p (D + 1)).1 labels labelUnits
    _ input.factors input.factors_nodup input.factors_complete input.data input.scopeIndex
    (GlobalPolynomial.interpolatedTable S coord coordUnits)
    input.color_eq input.table_eq input.origin_eq input.taylor_eq
    (SubexpActualRing.prime_power_zero p (D + 1))
    (SubexpActualRing.rho_ker p (D + 1) (Nat.succ_pos D)) hD
  · simpa only [Fintype.card_fin, GlobalPolynomial.interpolatedGlobalPolynomial] using
      SubexpCounting.interpolated_degree_lt S A coord coordUnits
        (by simpa only [Fintype.card_fin] using hD)
  · intro i
    change PolynomialAlgorithm.denote
      (((SubexpTableExecution.completeProgram ops.program p (D + 1)).1.map
        (List.map ops.decode)).getD i.val (List.map ops.decode [])) = _
    rw [List.getD_map]
    simpa only [SubexpDensePolynomial.decodeList] using
      SubexpTableExecution.completeProgram_correct ops p (D + 1)
        (Fact.out : p.Prime) (Nat.succ_pos D) baseMap i

/-- The zeroth coefficient consumed by the final word extractor is the
natural factor count represented in the selected prime-power ring. -/
theorem runSelected_coeff_zero (input : SelectedInput S L kops ops) (hD : 0 < D) :
    (PolynomialAlgorithm.denote ((runSelected S L kops ops input).1.map ops.decode)).coeff 0 =
      (Factor.count S : Λ) := by
  rw [runSelected_denote S L kops ops input hD, Polynomial.coeff_zero_eq_eval_zero]
  exact GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial S coord coordUnits
    (A).row (A).row_zero

/-- Equivalently, the actual represented output agrees with the existing
separated-count reconstruction value, before natural-number decoding. -/
theorem runSelected_eq_recoveredValue (input : SelectedInput S L kops ops) (hD : 0 < D) :
    (PolynomialAlgorithm.denote ((runSelected S L kops ops input).1.map ops.decode)).coeff 0 =
      SubexpCounting.explicitRecoveredValue S A coord
        (SubexpActualRing.rho_coordinateLift p (D + 1) (Nat.succ_pos D)) coordUnits
        sectionLift (D + 1) := by
  rw [runSelected_coeff_zero S L kops ops input hD]
  symm
  apply SubexpCounting.explicitRecoveredValue_eq_count
  · exact SubexpActualRing.prime_power_zero p (D + 1)
  · exact SubexpActualRing.rho_ker p (D + 1) (Nat.succ_pos D)
  · simpa only [Fintype.card_fin] using hD

/-- Decoding the represented constant coefficient recovers the entire
natural count, because its prime-power modulus exceeds every possible count. -/
theorem runSelected_decodeCount (input : SelectedInput S L kops ops) (hD : 0 < D) :
    SubexpActualRing.decodeCount p (D + 1) (Nat.succ_pos D)
      ((PolynomialAlgorithm.denote ((runSelected S L kops ops input).1.map
        ops.decode)).coeff 0) = Factor.count S := by
  rw [runSelected_coeff_zero S L kops ops input hD]
  exact SubexpActualRing.decodeCount_natCast p (D + 1) (Nat.succ_pos D) (Factor.count S)
    (by simpa only [Fintype.card_fin] using Counting.factor_count_lt_prime_power S)

end SelectedRing

end SubexponentialSAT.SubexpCountExecution

end OAI.Algorithms
