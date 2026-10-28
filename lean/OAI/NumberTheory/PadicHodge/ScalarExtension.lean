import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter

noncomputable section

/-! Scalar extension of actual summand operators. These lemmas retain
Frobenius on the original factor and transport generalized Hecke eigendata. -/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

variable {L : Type*} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]

/-- The GeometricComparison Frobenius inclusion identity remains valid after extending
coefficients to the algebraic closure for FrobeniusSlope. -/
theorem baseChange_summand_frobenius
    (Ω : Type*) [Field Ω] [Algebra L Ω]
    (S : Submodule L V) (φ : S ≃ₗ[L] S) (F : Module.End L V)
    (hφ : ∀ x : S, (φ x : V) = F (x : V)) :
    (S.subtype.baseChange Ω).comp (φ.toLinearMap.baseChange Ω) =
      (F.baseChange Ω).comp (S.subtype.baseChange Ω) := by
  have h : S.subtype.comp φ.toLinearMap = F.comp S.subtype := LinearMap.ext hφ
  simpa only [LinearMap.baseChange_comp] using
    congrArg (fun f : S →ₗ[L] V => f.baseChange Ω) h

/-- Every operator in a commuting family preserves its joint generalized
Hecke summand. -/
theorem hecke_summand_stable
    {I : Type*} (T : I → Module.End L V) (χ : I → L)
    (hcomm : ∀ i j, Commute (T i) (T j)) (i : I) :
    ∀ x ∈ GeometricComparison.Linear.generalizedHeckeSummand T χ, T i x ∈ GeometricComparison.Linear.generalizedHeckeSummand T χ := by
  intro x hx
  rw [GeometricComparison.Linear.mem_generalizedHeckeSummand] at hx ⊢
  intro j
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) (χ j) (hx j)

/-- The actual restriction of a Hecke operator to its simultaneous summand. -/
def restrictedHecke
    {I : Type*} (T : I → Module.End L V) (χ : I → L)
    (hcomm : ∀ i j, Commute (T i) (T j)) (i : I) :
    Module.End L (GeometricComparison.Linear.generalizedHeckeSummand T χ) :=
  (T i).restrict (hecke_summand_stable T χ hcomm i)

theorem restrictedHecke_generalized_eigenvalue
    {I : Type*} (T : I → Module.End L V) (χ : I → L)
    (hcomm : ∀ i j, Commute (T i) (T j)) (i : I) :
    (restrictedHecke T χ hcomm i).genEigenspace (χ i) ⊤ = ⊤ := by
  rw [restrictedHecke, Module.End.genEigenspace_restrict]
  apply top_unique
  intro x _
  exact (GeometricComparison.Linear.mem_generalizedHeckeSummand T χ x).mp x.property i

/-- Generalized scalar eigendata survives extension of coefficients,
without a semisimplicity assumption. -/
theorem baseChange_generalized_eigenvalue
    [FiniteDimensional L V]
    (Ω : Type*) [Field Ω] [Algebra L Ω]
    (F : Module.End L V) (a : L) (hF : F.genEigenspace a ⊤ = ⊤) :
    Module.End.genEigenspace (F.baseChange Ω) (algebraMap L Ω a) ⊤ = ⊤ := by
  have he : F.genEigenspace a (Module.finrank L V) = ⊤ :=
    top_unique (hF ▸ F.genEigenspace_le_genEigenspace_finrank a ⊤)
  have hz : (F - a • 1) ^ Module.finrank L V = 0 := by
    rw [Module.End.genEigenspace_nat] at he
    exact LinearMap.ker_eq_top.mp he
  have hz' := congrArg (fun f : Module.End L V => f.baseChange Ω) hz
  simp only [LinearMap.baseChange_pow, LinearMap.baseChange_sub,
    LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.baseChange_zero] at hz'
  have hz'' : (F.baseChange Ω - (algebraMap L Ω a) • 1) ^ Module.finrank L V = 0 := by
    simpa only [algebraMap_smul] using hz'
  apply top_unique
  apply le_trans _ ((Module.End.genEigenspace (F.baseChange Ω) (algebraMap L Ω a)).monotone
    (show (Module.finrank L V : ℕ∞) ≤ ⊤ from le_top))
  rw [Module.End.genEigenspace_nat, hz'', LinearMap.ker_zero]

/-- FrobeniusSlope's full generalized eigendata for scalar-extended native restrictions. -/
theorem scalar_extended_restrictedHecke_eigenvalue
    [FiniteDimensional L V]
    (Ω : Type*) [Field Ω] [Algebra L Ω]
    {I : Type*} (T : I → Module.End L V) (χ : I → L)
    (hcomm : ∀ i j, Commute (T i) (T j)) (i : I) :
    Module.End.genEigenspace ((restrictedHecke T χ hcomm i).baseChange Ω)
      (algebraMap L Ω (χ i)) ⊤ = ⊤ :=
  baseChange_generalized_eigenvalue Ω (restrictedHecke T χ hcomm i) (χ i)
    (restrictedHecke_generalized_eigenvalue T χ hcomm i)

end

end OAI.NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter
