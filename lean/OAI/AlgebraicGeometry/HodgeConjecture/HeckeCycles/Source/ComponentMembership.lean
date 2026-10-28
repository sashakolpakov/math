import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexPairing
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealStructure

/-! # Component Membership -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership.CM.Pairing

/-! Evaluate the actual source trace form on a single CM component. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

theorem conjugation_twice (τ : Gal(E/ℚ)) : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = τ := by
  apply AlgEquiv.ext
  intro x
  exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E (τ x)

def single (τ : Gal(E/ℚ)) (i : Fin 3) : GeometricSource.CM.Ambient E := Pi.single τ (Pi.single i 1)

omit [NumberField E] [NumberField.IsCMField E] in
theorem single_ne_zero (τ : Gal(E/ℚ)) (i : Fin 3) : Pairing.single E τ i ≠ 0 := by
  intro h
  have hi := congrArg (fun w : GeometricSource.CM.Ambient E => w τ i) h
  simp [Pairing.single] at hi

theorem pairing (b δ a : E) (τ : Gal(E/ℚ)) (i : Fin 3) :
    ComplexPairing.CM.ambientForm E b δ a (Pairing.single E τ i)
      (RealStructure.CM.conjugate E (Pairing.single E τ i)) =
        (((τ (δ * a) : E) : ℂ) * (if i = 2 then ((τ b : E) : ℂ) else 1)) := by
  rw [ComplexPairing.CM.ambientForm_apply, Finset.sum_eq_single τ]
  · rw [Finset.sum_eq_single i]
    · simp [Pairing.single, RealStructure.CM.conjugate, conjugation_twice]
    · intro j _ hji
      simp [Pairing.single, hji]
    · simp
  · intro σ _ hστ
    simp [Pairing.single, hστ]
  · simp

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership.CM.Pairing

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership.CM

/-! Explicit nonzero vectors in each selected source CM component. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership.CM.Pairing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (places : GeometricSource.CM.Places E)

def component (p : Fin places.count × Bool) : Gal(E/ℚ) :=
  if p.2 then ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative p.1 else places.representative p.1

theorem component_injective : Function.Injective (component E places) := places.complete.1

theorem single_other (i j : Fin places.count) (hji : j ≠ i) (a b : Bool) (k : Fin 3) :
    Pairing.single E (component E places (i, a)) k (component E places (j, b)) = 0 := by
  apply Pi.single_eq_of_ne
  intro h
  exact hji (congrArg Prod.fst (component_injective E places h))

theorem single_opposite (i : Fin places.count) (a : Bool) (k : Fin 3) :
    Pairing.single E (component E places (i, a)) k (component E places (i, !a)) = 0 := by
  apply Pi.single_eq_of_ne
  intro h
  have he := congrArg Prod.snd (component_injective E places h)
  cases a <;> simp at he

variable (B : GeometricSource.CM.BallDatum E) (d : Gal(E/ℚ) → Bool)

theorem compact_mem (i : Fin places.count) (hi : i ≠ places.distinguished) (z : GeometricSource.CM.BallChart) :
    GeometricSource.CM.prescribed E B places d z
      (Pairing.single E (component E places (i, d (places.representative i))) 0) := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [ite_eq_right hi]
    cases hd : d (places.representative i)
    · rw [ite_eq_right (by decide)]
      exact single_opposite E places i false 0
    · rw [ite_eq_left rfl]
      exact single_opposite E places i true 0
  · have h0 := single_other E places i j hji (d (places.representative i)) false 0
    have h1 := single_other E places i j hji (d (places.representative i)) true 0
    change Pairing.single E (component E places (i, d (places.representative i))) 0
      (places.representative j) = 0 at h0
    change Pairing.single E (component E places (i, d (places.representative i))) 0
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative j) = 0 at h1
    by_cases hj : j = places.distinguished
    · rw [ite_eq_left hj, h0, h1]
      exact ⟨Submodule.zero_mem _, by simp [GeometricSource.CM.localPairing]⟩
    · rw [ite_eq_right hj]
      split_ifs <;> assumption

theorem distinguished_mem : GeometricSource.CM.prescribed E B places d 0
    (Pairing.single E (component E places (places.distinguished, false)) 2) := by
  intro j
  by_cases hj : j = places.distinguished
  · subst j
    rw [ite_eq_left rfl]
    have h1 := single_opposite E places places.distinguished false 2
    change Pairing.single E (component E places (places.distinguished, false)) 2
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative places.distinguished) = 0 at h1
    rw [h1]
    constructor
    · simp only [Pairing.single, component, Bool.false_eq_true, ite_false, Pi.single_eq_same]
      have hv : (Pi.single 2 (1 : ℂ) : GeometricSource.CM.Vec ℂ) = GeometricSource.CM.BallDatum.lineVector (0 : GeometricSource.CM.BallChart) := by
        ext k
        fin_cases k <;> simp [GeometricSource.CM.BallDatum.lineVector]
      rw [hv]
      exact Submodule.mem_span_singleton_self _
    · simp [GeometricSource.CM.localPairing]
  · have h0 := single_other E places places.distinguished j hj false false 2
    have h1 := single_other E places places.distinguished j hj false true 2
    change Pairing.single E (component E places (places.distinguished, false)) 2
      (places.representative j) = 0 at h0
    change Pairing.single E (component E places (places.distinguished, false)) 2
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative j) = 0 at h1
    rw [ite_eq_right hj]
    split_ifs <;> assumption

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership.CM

end

end OAI
