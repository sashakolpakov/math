import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTExecution
import OAI.Algorithms.SubexponentialSAT.SubexpCounting
import OAI.Algorithms.SubexponentialSAT.SubexpHornerSemantics

namespace OAI.Algorithms

/-! Direct evaluation of the explicit Hermite reconstruction at zero. The
algorithm needs only local corrections and scalar Horner evaluations; no
global shifted polynomial or final polynomial division is required. -/

namespace SubexponentialSAT.SubexpCRTAtZero

open Polynomial
open scoped BigOperators

section WeightedExecution

open SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- One concrete quartic multiply-add in the outer reconstruction loop. -/
def weightedStep (t acc factor value : Quad (Word (baseWidth p μ))) :
    Quad (Word (baseWidth p μ)) :=
  (SubexpPreparedQuartic.binaryAdd p μ M acc
    (SubexpPreparedQuartic.binaryMul p μ M t factor value).1).1

/-- The accumulator used by the outer machine, with each factor and its
local Horner output supplied once. -/
def weightedFold (t : Quad (Word (baseWidth p μ)))
    (terms : List (Quad (Word (baseWidth p μ)) × Quad (Word (baseWidth p μ))))
    (acc : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) :=
  terms.foldl (fun acc term => weightedStep p μ M t acc term.1 term.2) acc

theorem weightedStep_decode (c : Fin 4 → ZMod (p^μ))
    (t acc factor value : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c) :
    SubexpHornerMachine.decode p μ c (weightedStep p μ M t acc factor value) =
      SubexpHornerMachine.decode p μ c acc +
        SubexpHornerMachine.decode p μ c factor * SubexpHornerMachine.decode p μ c value := by
  simp only [weightedStep, SubexpHornerMachine.decode,
    SubexpPreparedQuartic.binaryAdd_quotient,
    SubexpPreparedQuartic.binaryMul_quotient p μ M c t factor value ht]

theorem weightedFold_decode (c : Fin 4 → ZMod (p^μ))
    (t : Quad (Word (baseWidth p μ))) (ht : t.map (wordValue p μ) = reductionData c)
    (terms : List (Quad (Word (baseWidth p μ)) × Quad (Word (baseWidth p μ))))
    (acc : Quad (Word (baseWidth p μ))) :
    SubexpHornerMachine.decode p μ c (weightedFold p μ M t terms acc) =
      SubexpHornerMachine.decode p μ c acc +
        (terms.map (fun term => SubexpHornerMachine.decode p μ c term.1 *
          SubexpHornerMachine.decode p μ c term.2)).sum := by
  induction terms generalizing acc with
  | nil => simp [weightedFold]
  | cons term terms ih =>
      change SubexpHornerMachine.decode p μ c
        (weightedFold p μ M t terms (weightedStep p μ M t acc term.1 term.2)) = _
      rw [ih, weightedStep_decode p μ M c t acc term.1 term.2 ht]
      simp only [List.map_cons, List.sum_cons, add_assoc]

end WeightedExecution

noncomputable section

variable {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]

def value (θ : I → A) (D : ℕ) (a : I → A) (J : I → A[X]) : A :=
  ∑ i, (JetCRT.cofactor θ D i).eval 0 *
    (TruncatedInverse.correction θ D a J i).eval (-θ i)

theorem cofactor_eval_zero (θ : I → A) (D : ℕ) (i : I) :
    (JetCRT.cofactor θ D i).eval 0 =
      ∏ j ∈ Finset.univ.erase i, (-θ j)^D := by
  simp [JetCRT.cofactor, JetCRT.nodePower, eval_prod]

theorem value_scalar_cofactors (θ : I → A) (D : ℕ) (a : I → A) (J : I → A[X]) :
    value θ D a J = ∑ i, (∏ j ∈ Finset.univ.erase i, (-θ j)^D) *
      (TruncatedInverse.correction θ D a J i).eval (-θ i) := by
  simp only [value, cofactor_eval_zero]

theorem value_eq_eval (θ : I → A) (D : ℕ) (a : I → A) (J : I → A[X]) :
    value θ D a J = (TruncatedInverse.reconstruct θ D a J).eval 0 := by
  simp [value, TruncatedInverse.reconstruct, eval_finsetSum, eval_mul, eval_comp]

theorem value_eq_coeff (θ : I → A) (D : ℕ) (a : I → A) (J : I → A[X]) :
    value θ D a J = (TruncatedInverse.reconstruct θ D a J).coeff 0 := by
  rw [coeff_zero_eq_eval_zero, value_eq_eval]

theorem value_eq_target [Nontrivial A] [Nonempty I]
    (θ : I → A) (D : ℕ) (hD : 0 < D)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (a : I → A) (J : I → A[X])
    (ha : ∀ i, a i * (TruncatedInverse.localFactor θ D i).coeff 0 = 1)
    (H : A[X]) (hH : H.natDegree < Fintype.card I * D)
    (hJ : ∀ i, Truncation.trunc D (J i) = JetCRT.jet (θ i) D H) :
    value θ D a J = H.eval 0 := by
  rw [value_eq_eval, TruncatedInverse.reconstruct_eq θ D hD hθ a J ha H hH hJ]

theorem value_eq_crtProgram {C : Type*} (ops : SubexpSymbolicCost.RepresentedRing C A)
    {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C) (J : Fin Q → List C) :
    value (fun i => ops.decode (θ i)) D (fun i => ops.decode (a i))
        (fun i => PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops (J i))) =
      (PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops
        (SubexpCRTExecution.crtProgram ops.program θ D a J).1)).coeff 0 := by
  rw [SubexpCRTExecution.crtProgram_value, TruncatedInverse.denseCRT_denote, value_eq_coeff]

section WeightedReadback

open SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem weightedFold_value {Q : ℕ} (c : Fin 4 → ZMod (p^μ))
    (t zero : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hz : SubexpHornerMachine.decode p μ c zero = 0)
    (θ : Fin Q → LiftRing.Extension (QuarticSearch.poly c)) (D : ℕ)
    (a : Fin Q → LiftRing.Extension (QuarticSearch.poly c))
    (J : Fin Q → Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (factors values : Fin Q → Quad (Word (baseWidth p μ)))
    (hf : ∀ i, SubexpHornerMachine.decode p μ c (factors i) = (JetCRT.cofactor θ D i).eval 0)
    (hv : ∀ i, SubexpHornerMachine.decode p μ c (values i) =
      (TruncatedInverse.correction θ D a J i).eval (-θ i)) :
    SubexpHornerMachine.decode p μ c
      (weightedFold p μ M t (List.ofFn fun i => (factors i, values i)) zero) =
      value θ D a J := by
  rw [weightedFold_decode p μ M c t ht, hz, zero_add]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]
  simp_rw [hf, hv]
  rfl

theorem weightedFold_horner_value {Q : ℕ} (c : Fin 4 → ZMod (p^μ))
    (t zero : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hz : SubexpHornerMachine.decode p μ c zero = 0)
    (θ : Fin Q → LiftRing.Extension (QuarticSearch.poly c)) (D : ℕ)
    (a : Fin Q → LiftRing.Extension (QuarticSearch.poly c))
    (J : Fin Q → Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (factors points : Fin Q → Quad (Word (baseWidth p μ)))
    (P : Fin Q → List (Quad (Word (baseWidth p μ))))
    (hf : ∀ i, SubexpHornerMachine.decode p μ c (factors i) = (JetCRT.cofactor θ D i).eval 0)
    (hx : ∀ i, SubexpHornerMachine.decode p μ c (points i) = -θ i)
    (hP : ∀ i, PolynomialAlgorithm.denote ((P i).map (SubexpHornerMachine.decode p μ c)) =
      TruncatedInverse.correction θ D a J i) :
    SubexpHornerMachine.decode p μ c
      (weightedFold p μ M t (List.ofFn fun i => (factors i,
        SubexpHornerControl.fold (SubexpHornerMachine.stepValue p μ M t (points i))
          (P i).reverse zero)) zero) = value θ D a J := by
  apply weightedFold_value p μ M c t zero ht hz θ D a J factors _ hf
  intro i
  rw [SubexpHornerMachine.output_decode p μ M c t (points i) ht (P i) zero hz, hP i, hx i]

end WeightedReadback

section Selected

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) S.toPattern c)

/-- The selected-ring calculation as scalar evaluations of the local CRT
corrections. This is the same ring value as the existing full reconstruction. -/
def selectedValue : SubexpActualRing.Ring p (Fintype.card V + 1) :=
  let μ := Fintype.card V + 1
  let A := SubexpCounting.selectedLiftedLayout S L μ (Nat.succ_pos _)
  let lift := SubexpActualRing.coordinateLift p μ
  let hlift := SubexpActualRing.rho_coordinateLift p μ (Nat.succ_pos _)
  let units := SubexpActualRing.coordinateLift_unitDifferences p μ
  let sectionLift := SubexpActualRing.residueSection p μ (Nat.succ_pos _)
  value A.theta (Fintype.card V)
    (TruncatedInverse.constantInverse (Fintype.card V)
      (SubexpCounting.differenceInverse A sectionLift μ))
    (SubexpCounting.layoutJet A lift hlift sectionLift
      (GlobalPolynomial.interpolatedTable S lift units) μ (Fintype.card V))

def selectedNode (i : Fin c.Q) : SubexpActualRing.Ring p (Fintype.card V + 1) :=
  (SubexpCounting.selectedLiftedLayout S L (Fintype.card V + 1) (Nat.succ_pos _)).theta i

def selectedCofactor (i : Fin c.Q) : SubexpActualRing.Ring p (Fintype.card V + 1) :=
  (JetCRT.cofactor (selectedNode S L) (Fintype.card V) i).eval 0

def selectedCorrection (i : Fin c.Q) : Polynomial (SubexpActualRing.Ring p (Fintype.card V + 1)) :=
  let μ := Fintype.card V + 1
  let A := SubexpCounting.selectedLiftedLayout S L μ (Nat.succ_pos _)
  let lift := SubexpActualRing.coordinateLift p μ
  let hlift := SubexpActualRing.rho_coordinateLift p μ (Nat.succ_pos _)
  let units := SubexpActualRing.coordinateLift_unitDifferences p μ
  let sectionLift := SubexpActualRing.residueSection p μ (Nat.succ_pos _)
  TruncatedInverse.correction A.theta (Fintype.card V)
    (TruncatedInverse.constantInverse (Fintype.card V)
      (SubexpCounting.differenceInverse A sectionLift μ))
    (SubexpCounting.layoutJet A lift hlift sectionLift
      (GlobalPolynomial.interpolatedTable S lift units) μ (Fintype.card V)) i

omit [DecidableEq F] in
theorem selectedValue_eq_sum : selectedValue S L =
    ∑ i, selectedCofactor S L i * (selectedCorrection S L i).eval (-selectedNode S L i) := rfl

omit [DecidableEq F] in
theorem selectedValue_eq : selectedValue S L = SubexpCounting.selectedRingValue S L := by
  unfold selectedValue SubexpCounting.selectedRingValue SubexpCounting.explicitRecoveredValue
    SubexpCounting.explicitReconstruction
  exact value_eq_eval _ _ _ _

omit [DecidableEq F] in
theorem selectedValue_eq_count (hD : 0 < Fintype.card V) :
    selectedValue S L = (Factor.count S : SubexpActualRing.Ring p (Fintype.card V + 1)) := by
  rw [selectedValue_eq, SubexpCounting.selectedRingValue_eq_count S L hD]

open SubexpLiftRing SubexpQuarticRing in
omit [DecidableEq F] in
theorem weightedFold_selected_count
    (M : SubexpPreparedQuartic.Modulus p (Fintype.card V + 1))
    (t zero : Quad (Word (baseWidth p (Fintype.card V + 1))))
    (ht : t.map (wordValue p (Fintype.card V + 1)) =
      reductionData (QuarticSearch.liftedCoefficients p (Fintype.card V + 1)))
    (hz : SubexpHornerMachine.decode p (Fintype.card V + 1)
      (QuarticSearch.liftedCoefficients p (Fintype.card V + 1)) zero = 0)
    (factors values : Fin c.Q → Quad (Word (baseWidth p (Fintype.card V + 1))))
    (hf : ∀ i, SubexpHornerMachine.decode p (Fintype.card V + 1)
      (QuarticSearch.liftedCoefficients p (Fintype.card V + 1)) (factors i) = selectedCofactor S L i)
    (hv : ∀ i, SubexpHornerMachine.decode p (Fintype.card V + 1)
      (QuarticSearch.liftedCoefficients p (Fintype.card V + 1)) (values i) =
      (selectedCorrection S L i).eval (-selectedNode S L i))
    (hD : 0 < Fintype.card V) :
    SubexpHornerMachine.decode p (Fintype.card V + 1)
      (QuarticSearch.liftedCoefficients p (Fintype.card V + 1))
      (weightedFold p (Fintype.card V + 1) M t
        (List.ofFn fun i => (factors i, values i)) zero) =
      (Factor.count S : SubexpActualRing.Ring p (Fintype.card V + 1)) := by
  rw [weightedFold_decode _ _ _ _ _ ht, hz, zero_add]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]
  simp_rw [hf, hv]
  exact (selectedValue_eq_sum S L).symm.trans (selectedValue_eq_count S L hD)

end Selected

end

end SubexponentialSAT.SubexpCRTAtZero

end OAI.Algorithms
