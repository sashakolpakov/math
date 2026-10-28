import OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredComponents
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FilteredImage

/-! # Components -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Components

noncomputable section

section

/-! The independent projective Betti filtration is detected by the proved algebraic filtration images on its integral components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
local instance : Smooth P.toOver.hom := P.smooth
local instance : IsProper P.toOver.hom := P.projective.isProper
local instance (C : irreducibleComponents P.carrier) :
    IsIntegral (Betti.Smooth.Components.componentOver P.toOver C).left := Betti.Smooth.Components.componentOverIntegral P.toOver C
local instance (C : irreducibleComponents P.carrier) :
    Smooth (Betti.Smooth.Components.componentOver P.toOver C).hom := Betti.Smooth.Components.componentOverSmooth P.toOver C
local instance (C : irreducibleComponents P.carrier) :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Betti.Smooth.Components.componentOver P.toOver C)) := Betti.Smooth.ReferenceCongruence.componentMetrizable P.toOver C

theorem projectiveBettiFiltration_mem_iff_algebraicComponents (n : ℕ) (r : ℤ)
    (b : P.complexCohomology n) :
    b ∈ Target.projectiveBettiHodgeFiltration P n r ↔ Betti.Smooth.FilteredImage.smoothComponentFiltrationImage P.toOver n r b := by
  rw [ProjectiveFilteredComponents.Hodge.projectiveBettiFiltration_mem_iff_components]
  unfold Betti.Smooth.FilteredImage.smoothComponentFiltrationImage
  apply forall_congr'
  intro C
  have h := FilteredImage.Integration.projective_algebraicFiltration_image_iff (P.componentVariety C) n r
    (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n b C)
  have hX : (P.componentVariety C).toOver = Betti.Smooth.Components.componentOver P.toOver C := rfl
  have : IsIntegral (P.componentVariety C).toOver.left := (P.componentVariety C).property
  have : Smooth (P.componentVariety C).toOver.hom := (P.componentVariety C).presentation.smooth
  have : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (P.componentVariety C).toOver) :=
    IntegrationDerivedClass.projectivePointIntegrationMetrizable (P.componentVariety C)
  refine h.symm.trans ?_
  constructor
  · rintro ⟨a, ha, hab⟩
    exact ⟨a, ha, (eq_of_heq (Betti.Smooth.ReferenceCongruence.originalBettiComparison_congr hX n a a HEq.rfl)).symm.trans hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨a, ha, (eq_of_heq (Betti.Smooth.ReferenceCongruence.originalBettiComparison_congr hX n a a HEq.rfl)).trans hab⟩

end

/-! The original smooth projective de Rham-Betti map preserves the exact independently defined algebraic and Betti Hodge filtrations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

local instance : Smooth P.toOver.hom := P.smooth
local instance : IsProper P.toOver.hom := P.projective.isProper
local instance (C : irreducibleComponents P.carrier) :
    IsIntegral (Betti.Smooth.Components.componentOver P.toOver C).left := Betti.Smooth.Components.componentOverIntegral P.toOver C
local instance (C : irreducibleComponents P.carrier) :
    Smooth (Betti.Smooth.Components.componentOver P.toOver C).hom := Betti.Smooth.Components.componentOverSmooth P.toOver C
local instance (C : irreducibleComponents P.carrier) :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Betti.Smooth.Components.componentOver P.toOver C)) := Betti.Smooth.ReferenceCongruence.componentMetrizable P.toOver C

theorem smoothProjective_hodgeFiltration_comparison (n : ℕ) (r : ℤ) :
    (Target.algebraicHodgeFiltration P.toOver n r).map (Target.smoothDeRhamBettiLinearMap P.toOver n) =
      Target.projectiveBettiHodgeFiltration P n r := by
  ext b
  exact (Betti.Smooth.FilteredImage.smoothComparison_filtration_image_mem_iff P.toOver n r b).trans
    (projectiveBettiFiltration_mem_iff_algebraicComponents P n r b).symm

theorem projectivePresentation_hodgeFiltration_comparison
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsProper X.hom]
    (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (n : ℕ) (r : ℤ) :
    (Target.algebraicHodgeFiltration X n r).map (Target.smoothDeRhamBettiLinearMap X n) =
      Target.projectiveBettiHodgeFiltration (Target.projectivePresentation X Q) n r :=
  smoothProjective_hodgeFiltration_comparison (Target.projectivePresentation X Q) n r

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Components
