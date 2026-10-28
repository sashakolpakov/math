import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Character Field -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CharacterField

noncomputable section

/-! An arbitrary eigenvalue family with finite rational span lies in a finite local coefficient field. -/

variable {q : ℕ} [Fact q.Prime] {I : Type*}

def finiteCoefficientFieldOfFiniteSpan (χ : I → AlgebraicClosure ℚ_[q])
    (S : Submodule ℚ (AlgebraicClosure ℚ_[q])) [FiniteDimensional ℚ S]
    (hχ : ∀ i, χ i ∈ S) : Linear.FiniteHeckeCoefficientField q χ := by
  let b := Module.finBasis ℚ S
  let L := Linear.finiteCoefficientFieldOfFiniteFamily q (fun i => (b i : AlgebraicClosure ℚ_[q]))
  refine ⟨L.field, L.finite, ?_⟩
  let U : Submodule ℚ (AlgebraicClosure ℚ_[q]) := L.field.toSubalgebra.toSubmodule.restrictScalars ℚ
  have hb : (⊤ : Submodule ℚ S) ≤ U.comap S.subtype := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact L.contains i
  intro i
  exact hb (show (⟨χ i, hχ i⟩ : S) ∈ (⊤ : Submodule ℚ S) from trivial)

def finiteCoefficientFieldOfRationalCharacter
    {H : Type*} [CommRing H] [Algebra ℚ H]
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    [FiniteDimensional ℚ χ.toLinearMap.range]
    (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) :
    Linear.FiniteHeckeCoefficientField q (fun h => τ (χ h)) := by
  let f := τ.toRatAlgHom.toLinearMap
  let S := χ.toLinearMap.range.map f
  letI : FiniteDimensional ℚ S := Module.Finite.of_fg
    ((Submodule.FG.of_finite (N := χ.toLinearMap.range)).map f)
  exact finiteCoefficientFieldOfFiniteSpan (fun h => τ (χ h)) S
    (fun h => ⟨χ h, ⟨h, rfl⟩, rfl⟩)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CharacterField
