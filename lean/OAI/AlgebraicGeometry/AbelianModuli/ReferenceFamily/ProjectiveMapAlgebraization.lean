import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveScheme

/-! # Projective Map Algebraization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveMapAlgebraization

noncomputable section

/-! A continuous projective map with actual holomorphic coordinate
charts algebraizes on the original smooth projective variety. The
comparison is with the native complex points of the resulting morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {n : ℕ}
    (f : V.analyticSpace → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ i x, f x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      MDifferentiableAt 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin n → ℂ)
        (fun y => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) x)

local instance projectiveMapAlgebraization_integral : IsIntegral V.toOver.left := V.property
local instance projectiveMapAlgebraization_smooth : Smooth V.toOver.hom := V.presentation.smooth
local instance projectiveMapAlgebraization_targetIntegral : IsIntegral (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left :=
  ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth.isIntegral_projectiveSpace n
local instance projectiveMapAlgebraization_targetSmooth : Smooth (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom :=
  Albanese.Construction.ProjectiveCover.projectiveSpace_smooth n

include hf hd in
theorem nativeProjectiveMap_mdifferentiable :
    MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.NativeModel n)
      (fun x => ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f x)) := by
  let Y := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let : IsClosedImmersion (Over.Hom.left (𝟙 Y)) := by
    change IsClosedImmersion (𝟙 Y.left)
    infer_instance
  let g : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun x => (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (𝟙 Y) x)
  have hg : Continuous g := (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.continuous.comp
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (𝟙 Y))
  have hp : Continuous (fun x => ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f x)) :=
    (ComplexPoints.Analytic.ProjectiveScheme.continuous_projectivizationSchemePoint n).comp hf
  apply Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective.Constructions.ProjectiveManifoldComparison.mdifferentiable_of_common_embedding f g hg
    (fun x => ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f x)) hp
  · intro x
    change (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (𝟙 Y) (ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f x))) = f x
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_id]
    exact (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm_apply_apply (f x)
  · exact hd
  · intro i x hx
    exact ⟨ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap (𝟙 Y) i hx,
      ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_coordinatesOfSchemeMap_injective (𝟙 Y) i hx⟩

include hf hd in
theorem exists_algebraic_projectiveMap :
    ∃ g : V.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n),
      ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f x) := by
  let W := ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n
  let : IsProper V.toOver.hom := V.presentation.projective.isProper
  let : IsProper (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom := W.presentation.projective.isProper
  let : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) := V.presentation.projective.compactSpace_complexPoints
  exact Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization.exists_algebraic_map V.presentation.projective W.presentation.projective
    (fun x => ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f x)) (nativeProjectiveMap_mdifferentiable V f hf hd)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveMapAlgebraization
