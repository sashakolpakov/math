import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsStored
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm

namespace OAI.Algorithms

/-! A concrete dense Z-output list for CRT reconstruction. Its entries are
obtained only by sparse coefficient scans and a finite sum over retained U. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {R V : Type*} [CommSemiring R] [DecidableEq V]

def tabulate : ℕ → (ℕ → R) → List R
  | 0, _ => []
  | n+1, f => f 0 :: tabulate n (fun j => f (j+1))

omit [CommSemiring R] in
@[simp] theorem tabulate_length (n : ℕ) (f : ℕ → R) : (tabulate n f).length = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [tabulate, ih]

theorem coeff_tabulate (n : ℕ) (f : ℕ → R) (j : ℕ) :
    PolynomialAlgorithm.coeff (tabulate n f) j = if j < n then f j else 0 := by
  induction n generalizing f j with
  | zero => simp [tabulate, PolynomialAlgorithm.coeff]
  | succ n ih =>
      cases j with
      | zero => simp [tabulate, PolynomialAlgorithm.coeff]
      | succ j => simpa [tabulate, PolynomialAlgorithm.coeff] using ih (fun j => f (j+1)) j

def outputCoefficients (t J : ℕ) (l : Sparse.Data (Index V) R) : List R :=
  tabulate J (fun z => ∑ u ∈ Finset.range t, Sparse.fetch ⟨u, z, ∅⟩ l)

@[simp] theorem outputCoefficients_length (t J : ℕ) (l : Sparse.Data (Index V) R) :
    (outputCoefficients t J l).length = J := tabulate_length _ _

theorem outputCoefficients_denote (t J : ℕ) (l : Sparse.Data (Index V) R) :
    PolynomialAlgorithm.denote (outputCoefficients t J l) =
      Truncation.trunc J (sumUCoeff t (jetCoeff ⟨∅⟩ (Sparse.denote l))) := by
  ext z
  simp only [PolynomialAlgorithm.coeff_denote, outputCoefficients, coeff_tabulate,
    Truncation.coeff_trunc, sumUCoeff_coeff, jetCoeff_apply]
  by_cases hz : z < J
  · simp only [hz, ite_true]
    apply Finset.sum_congr rfl
    intro u hu
    exact (Sparse.jetCoeff_denote ⟨u, z, ∅⟩ l).symm
  · simp [hz]

theorem jetCoeff_empty_scalar (f : ScalarJet R) :
    jetCoeff (V := V) ⟨∅⟩ (jetScalar f) = f := by
  ext u z
  simp [jetCoeff_apply, jetScalar, scalar_empty]

theorem jetCoeff_projectSupport (s : Finset V) (f : Jet V R) :
    jetCoeff ⟨∅⟩ (projectSupport s f) = jetCoeff ⟨s⟩ f :=
  jetCoeff_empty_scalar _

theorem readout_canonical (t J : ℕ) (f : Jet V R) :
    Truncation.trunc J (sumUCoeff t (jetCoeff ⟨∅⟩ (canonical t J f))) =
      Truncation.trunc J (sumUCoeff t (jetCoeff ⟨∅⟩ f)) := by
  ext z
  by_cases hz : z < J
  · simp only [Truncation.coeff_trunc, hz, ite_true, sumUCoeff_coeff, jetCoeff_apply]
    apply Finset.sum_congr rfl
    intro u hu
    simp [coeff_canonical, Finset.mem_range.mp hu, hz]
  · simp [Truncation.coeff_trunc, hz]

/-- Clipping the local jet does not change any retained evaluated moment. -/
theorem evaluated_readout_canonical (t J : ℕ) (f : Jet V R)
    (x : V → R) (hx : ∀ v, x v * x v = x v) :
    Truncation.trunc J (sumUCoeff t (jetEval x hx (canonical t J f))) =
      Truncation.trunc J (sumUCoeff t (jetEval x hx f)) := by
  ext z
  by_cases hz : z < J
  · simp only [Truncation.coeff_trunc, hz, ite_true, sumUCoeff_coeff, jetEval_coeff]
    apply Finset.sum_congr rfl
    intro u hu
    simp [coeff_canonical, Finset.mem_range.mp hu, hz]
  · simp [Truncation.coeff_trunc, hz]

/-- The concrete list program computes the retained support coefficients of
the actual product of independently summed head records. -/
theorem run_output_denote {vars : Finset V} {t J : ℕ}
    (data : Finset V → List (List (R × Stored (R := R) vars t J)))
    (supports : List (Finset V)) :
    PolynomialAlgorithm.denote (outputCoefficients t J
      (MomentsAlgorithm.run Stored.ops data supports).1.data) =
      Truncation.trunc J (sumUCoeff t
        ((supports.map fun s => jetCoeff ⟨s⟩
          (((data s).map fun l =>
            (l.map fun a => ringScalar a.1 * a.2.denote).sum).prod)).sum)) := by
  rw [outputCoefficients_denote]
  change Truncation.trunc J (sumUCoeff t (jetCoeff ⟨∅⟩
    (Stored.denote (MomentsAlgorithm.run Stored.ops data supports).1))) = _
  rw [MomentsAlgorithm.run_canonical Stored.ops Stored.denote
    (ringScalar (V := V) (R := R)) (projectSupport (V := V) (R := R))
    (canonical t J) Stored.ops_correct data supports, readout_canonical]
  congr 2
  induction supports with
  | nil => simp
  | cons s ss ih => simp [List.map_cons, List.sum_cons, map_add, jetCoeff_projectSupport, ih]

/-- A direct implementation scans the stored list once for each (U,Z) slot.
This upper bound includes one addition per retained U coefficient. -/
def outputWork (t J : ℕ) (l : Sparse.Data (Index V) R) : ℕ :=
  J * t * (l.length + 1)

omit [CommSemiring R] in
theorem outputWork_bound {vars : Finset V} {t J : ℕ}
    (a : Stored (R := R) vars t J) :
    outputWork t J a.data ≤ J * t * (Stored.sizeBound vars t J + 1) :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right a.length_le 1)

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
