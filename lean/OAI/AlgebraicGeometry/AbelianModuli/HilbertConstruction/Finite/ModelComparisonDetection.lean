import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ProjectiveModelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomotopyBoundaryDetection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexEndpointHomotopy
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts

/-! # Model Comparison Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModelComparisonDetection

noncomputable section

/-! Actual maps of full complexes lift to bounded projective models.
Their residue boundary detection is preserved by the resulting homotopies. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R K : Type u} [CommRing R] [CommRing K]
variable {D C E₁ E₂ T₁ T₂ : CochainComplex (ModuleCat.{u} R) ℕ}

theorem finiteModel_exists_detecting_lifts
    [∀ q, Projective (D.X q)] (N : ℕ) (hN : ∀ q, N ≤ q → IsZero (D.X q))
    (p : D ⟶ C) (p₁ : E₁ ⟶ T₁) (p₂ : E₂ ⟶ T₂) [QuasiIso p₁] [QuasiIso p₂]
    (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂) (a : R →+* K)
    (hp : ShortComplex.QuasiIso
      ((ModuleCat.extendScalars a).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℕ) 0 1 2).map p)))
    (hd : Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars a).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℕ) 0 1 2).map r₁))
      ((ModuleCat.extendScalars a).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℕ) 0 1 2).map r₂))) :
    ∃ (g₁ : D ⟶ E₁) (g₂ : D ⟶ E₂),
      Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
        ((ModuleCat.extendScalars a).mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℕ) 0 1 2).map g₁))
        ((ModuleCat.extendScalars a).mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℕ) 0 1 2).map g₂)) := by
  obtain ⟨g₁, ⟨h₁⟩⟩ := Bounded.ProjectiveModelComparison.boundedProjective_exists_lift N hN p₁ (p ≫ r₁)
  obtain ⟨g₂, ⟨h₂⟩⟩ := Bounded.ProjectiveModelComparison.boundedProjective_exists_lift N hN p₂ (p ≫ r₂)
  let F := ModuleCat.extendScalars a
  let Q := HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℕ) 0 1 2
  have := hp
  refine ⟨g₁, g₂, HomotopyBoundaryDetection.CechBoundaryTransport.jointly_of_homotopy_square
    (F.mapShortComplex.map (Q.map g₁)) (F.mapShortComplex.map (Q.map g₂))
    (F.mapShortComplex.map (Q.map r₁)) (F.mapShortComplex.map (Q.map r₂))
    (F.mapShortComplex.map (Q.map p)) (F.mapShortComplex.map (Q.map p₁))
    (F.mapShortComplex.map (Q.map p₂)) ?_ ?_ hd⟩
  · have h := Quotients.FiniteDescent.ShortComplexEndpointHomotopy.Construction.LocalSectionLifting.shortComplexHomotopyMap F (h₁.symm.toShortComplex 1)
    have hQ : HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) 1 = Q := by
      unfold HomologicalComplex.shortComplexFunctor
      rw [show (ComplexShape.up ℕ).prev 1 = 0 by simp,
        show (ComplexShape.up ℕ).next 1 = 2 by simp]
    rw [hQ] at h
    simpa only [Functor.map_comp] using h
  · have h := Quotients.FiniteDescent.ShortComplexEndpointHomotopy.Construction.LocalSectionLifting.shortComplexHomotopyMap F (h₂.symm.toShortComplex 1)
    have hQ : HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) 1 = Q := by
      unfold HomologicalComplex.shortComplexFunctor
      rw [show (ComplexShape.up ℕ).prev 1 = 0 by simp,
        show (ComplexShape.up ℕ).next 1 = 2 by simp]
    rw [hQ] at h
    simpa only [Functor.map_comp] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModelComparisonDetection
