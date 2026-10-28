import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults
import Mathlib.Data.Fin.Tuple.Basic

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Coordinates.PairSwitches

noncomputable section

section

/-!
# PairSwitches: connectivity by pair switches, conditional on RiemannProjectivity

`hRiemannProjectivity` is the supplied realization proposition specialized to the given
Galois CM field. No statement stub is imported or used. BalancedMonomials is unnecessary
for this target: coordinatewise balance is already a natural hypothesis.
No additional substantive assumption is needed.

As in the committed statement, `w` is already negated in the conjugate
slots, and `OddFourFactorSwitch` allows changes to two types preserving
their pointwise sum. The existing combinatorial theorem constructs its
chain using transpositions on conjugate-pair representatives. The helper
below records that chain as a finite path; RiemannProjectivity realizes each of its types.
-/

open scoped BigOperators
open OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM

/-- Record a reflexive-transitive chain by its successive vertices. -/
theorem exists_fin_path_of_reflTransGen
    {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ (n : ℕ) (path : Fin (n + 1) → α),
      path 0 = a ∧ path (Fin.last n) = b ∧
      ∀ k : Fin n, r (path k.castSucc) (path k.succ) := by
  induction h with
  | refl =>
      exact ⟨0, fun _ => a, rfl, rfl, fun k => Fin.elim0 k⟩
  | @tail b c _ hbc ih =>
      obtain ⟨n, path, hzero, hlast, hstep⟩ := ih
      refine ⟨n + 1, Fin.snoc path c, ?_, Fin.snoc_last _ _, ?_⟩
      · simpa only [Fin.snoc_apply_zero] using hzero
      · intro k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simpa only [Fin.snoc_castSucc, Fin.succ_last,
            Fin.snoc_last, hlast] using hbc
        · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using hstep j

/-- The committed PairSwitches conclusion, conditional on the supplied RiemannProjectivity input. -/
theorem connectivity_by_pair_switches
    (E : IntermediateField ℚ ℂ)
    [NumberField E]
    [IsGalois ℚ E]
    [NumberField.IsCMField E]
    (hRiemannProjectivity : ∀ (u : Gal(E/ℚ) → Bool)
      (hu : ∀ τ : Gal(E/ℚ),
        u (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !(u τ)),
      Nonempty
        (ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E ⟨u, hu⟩)))
    (p : ℕ)
    (v w : Fin p →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hbalance : ∀ τ : Gal(E/ℚ),
      (∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((v i).val τ)) =
        ∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((w i).val τ)) :
    ∃ (n : ℕ)
      (path : Fin (n + 1) → Fin p →
        ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
          (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)),
      path 0 = v ∧
      path (Fin.last n) = w ∧
      (∀ k : Fin n,
        ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch (path k.castSucc) (path k.succ)) ∧
      (∀ (k : Fin (n + 1)) (i : Fin p),
        Nonempty
          (ComplexMultiplication.CMKnownResults.CM.HodgeRealization
            (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (path k i)))) := by
  classical
  let : LinearOrder Gal(E/ℚ) := linearOrderOfSTO WellOrderingRel
  let : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  have hchain : ComplexMultiplication.OddSignSwitch.CM.OddSwitchChain v w :=
    ComplexMultiplication.OddSignSwitch.CM.oddSwitchChain_of_signSum_eq
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)
      (ComplexMultiplication.ExteriorSignReduction.CM.CMCoefficientField.conjugation_mul_involutive E)
      (ComplexMultiplication.ExteriorSignReduction.CM.CMCoefficientField.conjugation_mul_ne E) v w hbalance
  obtain ⟨n, path, hzero, hlast, hstep⟩ :=
    exists_fin_path_of_reflTransGen hchain
  refine ⟨n, path, hzero, hlast, hstep, ?_⟩
  intro k i
  exact hRiemannProjectivity (path k i).val (path k i).property

end

/-!
# The coordinatewise transpositions in manuscript PairSwitches

A step swaps two slots at one coordinate and its conjugate and fixes every
other coordinate. Oddness supplies the opposite signs at the conjugate.
The finite path is lifted from the existing representative-coordinate
construction, so it also satisfies the historical four-factor relation.
-/

open scoped BigOperators
open OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM

/-- One transposition at a conjugate pair, with all other entries fixed. -/
def OddCoordinateTransposition {α κ : Type*} [DecidableEq κ]
    {ν : α → α} (v w : κ → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern ν) : Prop :=
  ∃ (t : α) (a b : κ),
    (∀ i, (w i).val t = (v (Equiv.swap a b i)).val t) ∧
    (∀ i, (w i).val (ν t) = (v (Equiv.swap a b i)).val (ν t)) ∧
    (∀ i x, x ≠ t → x ≠ ν t → (w i).val x = (v i).val x)

/-- Lifting a transposition exchanges both members of its conjugate pair. -/
theorem lift_coordinate_transposition
    {α κ : Type*} [LinearOrder α] [DecidableEq κ]
    (ν : α → α) (hν : Function.Involutive ν) (hne : ∀ x, ν x ≠ x)
    {v w : ComplexMultiplication.SignSwitch.CM.SignFamily κ (ComplexMultiplication.OddSignSwitch.CM.ConjugateRepresentative ν)}
    (h : ComplexMultiplication.SignSwitch.CM.CoordinateSwitch v w) :
    OddCoordinateTransposition
      (fun i => ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne (v i))
      (fun i => ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne (w i)) := by
  obtain ⟨t, a, b, rfl⟩ := h
  have ht (i : κ) :
      (ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne (ComplexMultiplication.SignSwitch.CM.permuteAt v t (Equiv.swap a b) i)).val t =
        (ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne (v (Equiv.swap a b i))).val t := by
    change ComplexMultiplication.OddSignSwitch.CM.extendOddSign ν hν hne _ t = ComplexMultiplication.OddSignSwitch.CM.extendOddSign ν hν hne _ t
    simp only [ComplexMultiplication.OddSignSwitch.CM.extendOddSign_representative, ComplexMultiplication.SignSwitch.CM.permuteAt, ite_true]
  refine ⟨t, a, b, ht, ?_, ?_⟩
  · intro i
    rw [(ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne (ComplexMultiplication.SignSwitch.CM.permuteAt v t (Equiv.swap a b) i)).property,
      (ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne (v (Equiv.swap a b i))).property, ht]
  · intro i x hxt hxct
    change ComplexMultiplication.OddSignSwitch.CM.extendOddSign ν hν hne _ x = ComplexMultiplication.OddSignSwitch.CM.extendOddSign ν hν hne _ x
    by_cases hx : x < ν x
    · have hrep : (⟨x, hx⟩ : ComplexMultiplication.OddSignSwitch.CM.ConjugateRepresentative ν) ≠ t := by
        intro heq
        exact hxt (congrArg Subtype.val heq)
      simp only [ComplexMultiplication.OddSignSwitch.CM.extendOddSign, dite_eq_left hx, ComplexMultiplication.SignSwitch.CM.permuteAt, ite_eq_right hrep]
    · have hrep :
          (⟨ν x, ComplexMultiplication.OddSignSwitch.CM.conjugate_lt_of_not_lt ν hν hne x hx⟩ :
            ComplexMultiplication.OddSignSwitch.CM.ConjugateRepresentative ν) ≠ t := by
        intro heq
        apply hxct
        have heq' := congrArg (fun u : ComplexMultiplication.OddSignSwitch.CM.ConjugateRepresentative ν => ν u.val) heq
        simpa only [hν x] using heq'
      simp only [ComplexMultiplication.OddSignSwitch.CM.extendOddSign, dite_eq_right hx, ComplexMultiplication.SignSwitch.CM.permuteAt, ite_eq_right hrep]

/-- Equal coordinate sums give a finite path of actual coordinate swaps;
the very same steps satisfy the historical four-factor switch relation. -/
theorem coordinate_path_of_signSum_eq
    {α κ : Type*} [LinearOrder α] [Fintype α] [Fintype κ] [DecidableEq κ]
    (ν : α → α) (hν : Function.Involutive ν) (hne : ∀ x, ν x ≠ x)
    (v w : κ → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern ν)
    (hs : ∀ x, (∑ i, ComplexMultiplication.SignSwitch.CM.signValue ((v i).val x)) =
      ∑ i, ComplexMultiplication.SignSwitch.CM.signValue ((w i).val x)) :
    ∃ (n : ℕ) (path : Fin (n + 1) → κ → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern ν),
      path 0 = v ∧ path (Fin.last n) = w ∧
      (∀ k : Fin n, OddCoordinateTransposition (path k.castSucc) (path k.succ)) ∧
      (∀ k : Fin n, ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch (path k.castSucc) (path k.succ)) := by
  let v₀ : ComplexMultiplication.SignSwitch.CM.SignFamily κ (ComplexMultiplication.OddSignSwitch.CM.ConjugateRepresentative ν) := fun i x => (v i).val x
  let w₀ : ComplexMultiplication.SignSwitch.CM.SignFamily κ (ComplexMultiplication.OddSignSwitch.CM.ConjugateRepresentative ν) := fun i x => (w i).val x
  have h : ComplexMultiplication.SignSwitch.CM.SwitchChain v₀ w₀ := ComplexMultiplication.SignSwitch.CM.switchChain_of_signSum_eq (fun x => hs x)
  obtain ⟨n, q, hzero, hlast, hstep⟩ := exists_fin_path_of_reflTransGen h
  refine ⟨n, (fun k i => ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne (q k i)), ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [hzero]
    funext i
    exact (ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne).apply_symm_apply (v i)
  · dsimp only
    rw [hlast]
    funext i
    exact (ComplexMultiplication.OddSignSwitch.CM.oddSignEquiv ν hν hne).apply_symm_apply (w i)
  · intro k
    exact lift_coordinate_transposition ν hν hne (hstep k)
  · intro k
    exact (hstep k).oddFourFactor ν hν hne

/-- Negating a slot type compensates exactly for the conjugate embedding. -/
theorem neg_type_conjugate_sign {α : Type*} {ν : α → α}
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern ν) (x : α) : v.neg.val (ν x) = v.val x := by
  simp only [ComplexMultiplication.OddSignSwitch.CM.OddSignPattern.neg_apply, v.property, Bool.not_not]

/-- The balanced `2p` source slots supply the two lists in PairSwitches. -/
theorem balanced_slots_signSum {α : Type*} {ν : α → α} (p : ℕ)
    (v : Fin (p + p) → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern ν)
    (hs : ∀ x, (∑ i, ComplexMultiplication.SignSwitch.CM.signValue ((v i).val x)) = 0) :
    ∀ x, (∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((v (Fin.castAdd p i)).val x)) =
      ∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((v (Fin.natAdd p i)).neg.val x) := by
  intro x
  have hx := hs x
  rw [Fin.sum_univ_add] at hx
  simp only [ComplexMultiplication.OddSignSwitch.CM.OddSignPattern.neg_apply, ComplexMultiplication.SignSwitch.CM.signValue_not, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.Coordinates.PairSwitches
