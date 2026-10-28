import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianFormula
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyMatrixCoordinates

/-! # Cayley Gaussian Cutoffs -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyGaussianCutoffs.Construction

noncomputable section

/-! The determinant Gaussian formula in arbitrary symplectic coordinates,
ready to apply to the actual Cayley operators. -/

open _root_.Matrix _root_.MeasureTheory

theorem unitaryCayley_hasGaussianCutoffs
    {F E V : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [MeasurableSpace V] [BorelSpace V]
    (hE : ¬ DiscreteTopology E) (hQuadratic : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ a : Fˣ, GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => (a : F) * Algebra.norm F x)
      (GaussianCutoffHaar.Construction.normGaussianValue ω Γ a))
    (ν : Measure V) [ν.IsAddHaarMeasure] [ν.Regular]
    {d : ℕ} (Q : Matrix (Fin d) (Fin d) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (g h : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q) (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (b : Fˣ) (hb : algebraMap F E (b : F) = (CayleyProduct.Construction.unitaryProductForm σ Q g h).det)
    (β : LinearMap.BilinForm F V) (e : (Fin d → E) ≃ₜ+ V)
    (he : ∀ x y, β (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2)
    (Dg Dh : V ≃ₗ[F] V)
    (hDg : ∀ x, Dg (e x) = e (((g.val : Matrix (Fin d) (Fin d) E) - 1) *ᵥ x))
    (hDh : ∀ x, Dh (e x) = e (((h.val : Matrix (Fin d) (Fin d) E) - 1) *ᵥ x)) :
    ∃ Z : ℂ, Z ≠ 0 ∧ GaussianCutoff.Construction.HasGaussianCutoffs ν ψ
      (fun x => CayleyCompositionPhase.Construction.cayleyWeylPhase β Dg x + CayleyCompositionPhase.Construction.cayleyWeylPhase β Dh x) Z ∧
      DiagonalNormGaussian.Construction.gaussianPhase Z = (GaussianFormula.Construction.normWeilConstant ω Γ hΓ0 : ℂ) ^ d * (ω b : ℂ) := by
  let : SecondCountableTopology E := TestSpaceAnalysis.Construction.localField_secondCountable E hE
  let μ : Measure (Fin d → E) := ν.map e.symm
  let : μ.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map ν
  let : μ.Regular := Measure.Regular.map e.symm.toHomeomorph
  obtain ⟨Z, hZ, hcut, hphase⟩ := GaussianFormula.Construction.unitary_product_hasGaussianCutoffs hE hQuadratic σ hne ω hω
    μE ψ Γ hΓ0 hΓ μ Q hQ hskew g h hg hh hgh b hb
  have ht := hcut.transport e.symm ν ψ
    (HermitianNormForms.Construction.hermitianTraceQuadratic σ (GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ Q g h)) Z
  have heq : (fun x => HermitianNormForms.Construction.hermitianTraceQuadratic σ (GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ Q g h) (e.symm x)) =
      fun x => CayleyCompositionPhase.Construction.cayleyWeylPhase β Dg x + CayleyCompositionPhase.Construction.cayleyWeylPhase β Dh x := by
    funext x
    have hx := CayleyMatrixCoordinates.Construction.cayleyWeylPhase_unitary_sum_coordinates σ (TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ)
      Q hQ hskew g h hg hh hgh β e he Dg Dh hDg hDh (e.symm x)
    rw [e.apply_symm_apply] at hx
    exact hx.symm
  rw [heq] at ht
  exact ⟨Z, hZ, ht, hphase⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyGaussianCutoffs.Construction
