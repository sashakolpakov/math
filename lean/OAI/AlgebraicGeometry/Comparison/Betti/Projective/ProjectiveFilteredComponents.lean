import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFormFiltration
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Filtration

/-! # Projective Filtered Components -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ProjectiveFilteredComponents.Hodge

noncomputable section

section

/-! The manifold filtration used by the filtered analytic sheaves is
exactly HodgeDecomposition's independently defined filtration on projective component forms. -/

open scoped _root_.Manifold ContDiff

theorem componentProjection_apply_manifold (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (a : P.componentForms n) (C : irreducibleComponents P.carrier) :
    Analysis.HodgeTheory.Decomposition.Projectors.Constructions.componentProjection P n i a C =
      ManifoldFormFiltration.Hodge.manifoldTypeProjection (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n i (a C) :=
  Analysis.HodgeTheory.Decomposition.Projectors.Constructions.spectralProjector_intertwine (Analysis.HodgeTheory.Decomposition.Types.Constructions.componentAction P n) Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter
    (Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter_injective n) Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction
    (LinearMap.proj C) (fun _ _ => rfl) i a

theorem mem_projectiveFilteredForms_iff_components (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (r : ℤ) (a : P.componentForms n) :
    a ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.filteredForms P n r ↔ ∀ C : irreducibleComponents P.carrier,
      a C ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n r := by
  rw [Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.mem_filteredForms_iff_projections]
  constructor
  · intro ha C
    rw [ManifoldFormFiltration.Hodge.mem_manifoldFormFiltration_iff_projections]
    intro i hi
    rw [← componentProjection_apply_manifold]
    exact congrFun (ha i hi) C
  · intro ha i hi
    funext C
    rw [componentProjection_apply_manifold]
    exact (ManifoldFormFiltration.Hodge.mem_manifoldFormFiltration_iff_projections
      (P.componentVariety C).analyticModel (P.componentVariety C).analyticSpace n r (a C)).mp
        (ha C) i hi

def projectiveComponentFormFiltration (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (r : ℤ) :
    Submodule ℂ (P.componentForms n) :=
  Submodule.pi Set.univ fun C =>
    ManifoldFormFiltration.Hodge.manifoldFormFiltration (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace n r

theorem projectiveComponentFormFiltration_eq (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (r : ℤ) : projectiveComponentFormFiltration P n r = Analysis.HodgeTheory.Decomposition.Core.Constructions.filteredForms P n r := by
  ext a
  rw [mem_projectiveFilteredForms_iff_components]
  simp only [projectiveComponentFormFiltration, Submodule.mem_pi, Set.mem_univ, forall_true_left]

/-- The original independent Betti filtration is the class image of closed
forms in the actual componentwise smooth Hodge filtration. -/
theorem projectiveBettiFiltration_eq_componentFilteredClasses (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (r : ℤ) :
    Target.projectiveBettiHodgeFiltration P n r =
      ((projectiveComponentFormFiltration P n r).comap (P.componentClosedForms n).subtype).map
        (P.closedFormBettiClass n) := by
  rw [projectiveComponentFormFiltration_eq,
    Filtration.projectiveBettiHodgeFiltration_eq_closedSmoothFiltration]
  rfl

end

/-! The independently defined projective Betti filtration is detected by
closed filtered representatives on its actual integral components. -/

open _root_.CategoryTheory

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (r : ℤ)

theorem componentClosedForm_filtered_iff (a : P.componentClosedForms n) :
    a ∈ (projectiveComponentFormFiltration P n r).comap (P.componentClosedForms n).subtype ↔
      ∀ C : irreducibleComponents P.carrier,
        (P.componentClosedFormsEquiv n a C).val ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration
          (P.componentVariety C).analyticModel (P.componentVariety C).analyticSpace n r := by
  change a.val ∈ projectiveComponentFormFiltration P n r ↔ _
  simp only [projectiveComponentFormFiltration, Submodule.mem_pi, Set.mem_univ, forall_true_left]
  rfl

theorem projectiveBettiFiltration_mem_iff_components (b : P.complexCohomology n) :
    b ∈ Target.projectiveBettiHodgeFiltration P n r ↔
      ∀ C : irreducibleComponents P.carrier,
        ∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (P.componentVariety C).analyticModel
            (P.componentVariety C).analyticSpace n,
          a.val ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration (P.componentVariety C).analyticModel
            (P.componentVariety C).analyticSpace n r ∧
          ((P.componentVariety C).deRhamBettiIso n).hom ((P.componentVariety C).deRhamClass n a) =
            P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n b C := by
  rw [projectiveBettiFiltration_eq_componentFilteredClasses, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, hab⟩ C
    refine ⟨P.componentClosedFormsEquiv n a C, (componentClosedForm_filtered_iff P n r a).1 ha C, ?_⟩
    rw [← P.componentBettiEquiv_closedFormBettiClass, hab]
  · intro h
    choose a ha hab using h
    let c := (P.componentClosedFormsEquiv n).symm a
    have hc : P.componentClosedFormsEquiv n c = a := (P.componentClosedFormsEquiv n).apply_symm_apply a
    refine ⟨c, (componentClosedForm_filtered_iff P n r c).2 ?_, ?_⟩
    · intro C
      rw [hc]
      exact ha C
    · apply (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n).injective
      funext C
      rw [P.componentBettiEquiv_closedFormBettiClass, hc]
      exact hab C

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ProjectiveFilteredComponents.Hodge
