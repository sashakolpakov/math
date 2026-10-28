import OAI.Analysis.HodgeTheory.Decomposition.WeakHarmonics
import OAI.Analysis.HodgeTheory.Decomposition.WeakGraphInversion
import OAI.Analysis.HodgeTheory.Decomposition.PoissonOperators

/-! # Weak Equation -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakEquation.Constructions

noncomputable section

section

/-! Unconditional normalized weak Poisson inversion after subtracting the
actual finite-dimensional weak harmonic projection. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

abbrev ProjectiveNormalizedEnergy :=
  Submodule.orthogonal (𝕜 := ℂ) (E := EnergyDomain.Constructions.ProjectiveEnergyDomain V n) (WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n)

theorem projective_weak_poisson_existsUnique (f : Form.Constructions.ProjectiveL2Forms V (n + 1))
    (hf : ∀ k : EnergyDomain.Constructions.ProjectiveEnergyDomain V n, EnergyDomain.Constructions.projectiveEnergyDerivative V n k = 0 →
      inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n k) = 0) :
    ∃! u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n,
      (∀ k, EnergyDomain.Constructions.projectiveEnergyDerivative V n k = 0 → inner ℂ k u = 0) ∧ ∀ v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n,
      inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n u) (EnergyDomain.Constructions.projectiveEnergyDerivative V n v) =
        inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) :=
  PoissonOperators.Constructions.projectiveGraphWeakEquationSolver V n f hf

theorem projective_weak_green_existsUnique (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    ∃! u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n,
      (∀ k, EnergyDomain.Constructions.projectiveEnergyDerivative V n k = 0 → inner ℂ k u = 0) ∧ ∀ v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n,
      inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n u) (EnergyDomain.Constructions.projectiveEnergyDerivative V n v) =
        inner ℂ (f - WeakHarmonics.Constructions.projectiveWeakHarmonicInclusion V n (WeakHarmonics.Constructions.projectiveWeakHarmonicPart V n f))
          (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) :=
  projective_weak_poisson_existsUnique V n _ (fun k hk => WeakHarmonics.Constructions.projectiveWeakHarmonicPart_remainder_orthogonal V n f ⟨k, hk⟩)

def projectiveWeakGreenSolution (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) : EnergyDomain.Constructions.ProjectiveEnergyDomain V n :=
  (projective_weak_green_existsUnique V n f).choose

theorem projectiveWeakGreenSolution_normalized (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    ∀ k, EnergyDomain.Constructions.projectiveEnergyDerivative V n k = 0 → inner ℂ k (projectiveWeakGreenSolution V n f) = 0 :=
  (projective_weak_green_existsUnique V n f).choose_spec.1.1

theorem projectiveWeakGreenSolution_pair (f : Form.Constructions.ProjectiveL2Forms V (n + 1))
    (v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n (projectiveWeakGreenSolution V n f))
      (EnergyDomain.Constructions.projectiveEnergyDerivative V n v) +
      inner ℂ (WeakHarmonics.Constructions.projectiveWeakHarmonicInclusion V n (WeakHarmonics.Constructions.projectiveWeakHarmonicPart V n f))
        (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) = inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) := by
  have h : inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n (projectiveWeakGreenSolution V n f))
      (EnergyDomain.Constructions.projectiveEnergyDerivative V n v) =
      inner ℂ (f - WeakHarmonics.Constructions.projectiveWeakHarmonicInclusion V n (WeakHarmonics.Constructions.projectiveWeakHarmonicPart V n f))
        (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) := (projective_weak_green_existsUnique V n f).choose_spec.1.2 v
  have hsub := inner_sub_left (𝕜 := ℂ) f
    (WeakHarmonics.Constructions.projectiveWeakHarmonicInclusion V n (WeakHarmonics.Constructions.projectiveWeakHarmonicPart V n f)) (EnergyDomain.Constructions.projectiveEnergyInclusion V n v)
  exact eq_sub_iff_add_eq.mp (h.trans hsub)

end

/-! The actual weak harmonic forms and weak Green solution satisfy the
completed manifold Hodge equation with their genuine L² forcing. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

def IsProjectiveWeakHodgeSolution (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n)
    (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) : Prop :=
  ∀ v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n,
    inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n u) (EnergyDomain.Constructions.projectiveEnergyDerivative V n v) =
      inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n v)

theorem projectiveWeakHarmonic_is_weak_solution (u : WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n) :
    IsProjectiveWeakHodgeSolution V n u.val 0 := by
  intro v
  have hu : EnergyDomain.Constructions.projectiveEnergyDerivative V n u.val = 0 := u.property
  rw [hu, inner_zero_left, inner_zero_left]

theorem projectiveWeakGreen_is_weak_solution (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    IsProjectiveWeakHodgeSolution V n (projectiveWeakGreenSolution V n f)
      (f - WeakHarmonics.Constructions.projectiveWeakHarmonicInclusion V n (WeakHarmonics.Constructions.projectiveWeakHarmonicPart V n f)) :=
  (projective_weak_green_existsUnique V n f).choose_spec.1.2

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakEquation.Constructions
