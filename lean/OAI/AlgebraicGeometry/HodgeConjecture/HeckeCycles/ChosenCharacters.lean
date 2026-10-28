import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Characters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate

/-! # Chosen Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

noncomputable section

/-! Algebraic character lifts for the complex embedding already chosen
by CMPoints. Finite-field automorphisms lift through this same embedding. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Characters.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.GaloisLift

def embeddedClosure (j : AlgebraicClosure ℚ →+* ℂ) :
    AlgebraicClosure ℚ →ₐ[ℚ] Coefficients.CM.algebraicField := by
  let : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  exact j.toRatAlgHom.codRestrict Coefficients.CM.algebraicField.toSubalgebra
    (fun a => mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom j.toRatAlgHom))

def chosenClosureEquiv (j : AlgebraicClosure ℚ →+* ℂ) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] Coefficients.CM.algebraicField := by
  let : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  exact AlgEquiv.ofBijective (embeddedClosure j)
    (Algebra.IsAlgebraic.algHom_bijective₂ (embeddedClosure j) Characters.CM.closureEquiv.symm.toAlgHom).1

theorem chosenClosureEquiv_apply (j : AlgebraicClosure ℚ →+* ℂ) (a : AlgebraicClosure ℚ) :
    (chosenClosureEquiv j a : ℂ) = j a := rfl

theorem chosenClosureEquiv_inverse (j : AlgebraicClosure ℚ →+* ℂ) (a : Coefficients.CM.algebraicField) :
    j ((chosenClosureEquiv j).symm a) = (a : ℂ) :=
  congrArg (fun a : Coefficients.CM.algebraicField => (a : ℂ)) ((chosenClosureEquiv j).apply_symm_apply a)

variable {U H : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
  [CommRing H] [Algebra ℚ H]

def chosenCharacter (j : AlgebraicClosure ℚ →+* ℂ)
    (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) :
    H →ₐ[ℚ] AlgebraicClosure ℚ :=
  (chosenClosureEquiv j).symm.toAlgHom.comp (Characters.CM.algebraicCharacter T χ hχ)

theorem chosenCharacter_apply (j : AlgebraicClosure ℚ →+* ℂ)
    (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) (h : H) :
    j (chosenCharacter j T χ hχ h) = χ h :=
  chosenClosureEquiv_inverse j (Characters.CM.algebraicCharacter T χ hχ h)

theorem chosenCharacter_jointSpace (j : AlgebraicClosure ℚ →+* ℂ)
    (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) :
    HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ)
      (fun h => j (chosenCharacter j T χ hχ h)) =
      HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ := by
  simp only [chosenCharacter_apply]

def chosenAutomorphism (j : AlgebraicClosure ℚ →+* ℂ) (τ : Gal(Coefficients.CM.algebraicField/ℚ)) :
    Gal(AlgebraicClosure ℚ/ℚ) :=
  (chosenClosureEquiv j).trans (τ.trans (chosenClosureEquiv j).symm)

theorem chosenAutomorphism_apply (j : AlgebraicClosure ℚ →+* ℂ)
    (τ : Gal(Coefficients.CM.algebraicField/ℚ)) (a : AlgebraicClosure ℚ) :
    j (chosenAutomorphism j τ a) = (τ (chosenClosureEquiv j a) : ℂ) :=
  chosenClosureEquiv_inverse j _

theorem chosenAutomorphism_character (j : AlgebraicClosure ℚ →+* ℂ)
    (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → Coefficients.CM.algebraicField)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) (fun h => (χ h : ℂ)) ≠ ⊥)
    (τ : Gal(Coefficients.CM.algebraicField/ℚ)) (h : H) :
    j (chosenAutomorphism j τ (chosenCharacter j T (fun h => (χ h : ℂ)) hχ h)) =
      (τ (χ h) : ℂ) := by
  rw [chosenAutomorphism_apply]
  apply congrArg (fun a : Coefficients.CM.algebraicField => (τ a : ℂ))
  apply Subtype.ext
  exact (chosenClosureEquiv_apply j _).trans (chosenCharacter_apply j T _ hχ h)

/-- The automorphism lift respects the chosen complex embedding on every
element of the finite coefficient field. -/
theorem chosen_conjugate_lift (j : AlgebraicClosure ℚ →+* ℂ)
    (K : IntermediateField ℚ ℂ) [NumberField K] (σ : Gal(K/ℚ)) :
    ∃ τ : Gal(AlgebraicClosure ℚ/ℚ), ∀ a : K,
      j (τ ((chosenClosureEquiv j).symm
        (IntermediateField.inclusion (ScalarConjugate.CM.GaloisLift.le_algebraicField K) a))) = (σ a : ℂ) := by
  obtain ⟨τ, hτ⟩ := ScalarConjugate.CM.GaloisLift.exists_algebraic_lift K σ
  let e := chosenClosureEquiv j
  refine ⟨e.trans (τ.trans e.symm), ?_⟩
  intro a
  change j (e.symm (τ (e (e.symm _)))) = _
  rw [e.apply_symm_apply, chosenClosureEquiv_inverse]
  exact hτ a

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
