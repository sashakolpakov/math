import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphProjective
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteNormalIso

/-! # Holomorphic Algebraization Graph -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization

noncomputable section

/-! # RiemannProjectivity: a holomorphic graph determines an actual algebraic morphism -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Manifold
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProper X.hom] [IsProper Y.hom]
  [CompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

theorem exists_reduced_closed_graph_subscheme
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom)
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : MDifferentiable (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model Y)) (fun x => f x)) :
    ∃ (Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (i : Z ⟶ (X ⊗ Y)),
      IsReduced Z.left ∧ IsClosedImmersion i.left ∧ IsProper Z.hom ∧
      ∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y),
        p ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ↔
          f (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CartesianMonoidalCategory.fst X Y) p) =
            AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CartesianMonoidalCategory.snd X Y) p := by
  let a₀ : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension) := Over.homMk P.embedding P.over_base
  let b₀ : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.ambientDimension) := Over.homMk Q.embedding Q.over_base
  let : IsClosedImmersion a₀.left := P.closedImmersion
  let : IsClosedImmersion b₀.left := Q.closedImmersion
  let π₁ := CartesianMonoidalCategory.fst X Y
  let π₂ := CartesianMonoidalCategory.snd X Y
  let a := π₁ ≫ a₀
  let b := π₂ ≫ b₀
  obtain ⟨R, degree, hQ, hgraph⟩ := HolomorphicGraphProjective.Constructions.HolomorphicGraphEquations.projective_equations a₀ b₀ f hf
  obtain ⟨Z, i, hZ, hi, himage⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme.Constructions.Algebraization.exists_reduced_closed_subscheme_of_segre_equations
    a b (fun q : R => q.val) degree hQ
  let : IsClosedImmersion i.left := hi
  have hproperProd : IsProper (X ⊗ Y).hom := by dsimp; infer_instance
  let : IsProper (X ⊗ Y).hom := hproperProd
  have hproperZ : IsProper Z.hom := by
    rw [← i.w]
    infer_instance
  refine ⟨Z, i, hZ, hi, hproperZ, ?_⟩
  intro p
  have hg : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme.Constructions.Algebraization.segreOfSchemeMaps a b p =
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.segre (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding a₀ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p))
        (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding b₀ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₂ p)) := by
    simp only [a, b, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme.Constructions.Algebraization.segreOfSchemeMaps]
    rfl
  rw [himage]
  change AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme.Constructions.Algebraization.segreOfSchemeMaps a b p ∈ AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus
    (fun q : R => q.val) degree hQ ↔ _
  rw [← hgraph, hg]
  constructor
  · rintro ⟨x, hx⟩
    have heq : (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding a₀ x, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding b₀ (f x)) =
        (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding a₀ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p),
          HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding b₀ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₂ p)) :=
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.segre_injective hx
    have hx₁ : x = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p :=
      (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding_closed a₀).injective (congrArg Prod.fst heq)
    have hx₂ : f x = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₂ p :=
      (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding_closed b₀).injective (congrArg Prod.snd heq)
    rwa [hx₁] at hx₂
  · intro h
    refine ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p, ?_⟩
    change AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.segre (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding a₀ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p))
      (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding b₀ (f (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p))) = _
    rw [h]

/-- The algebraic graph supplies a proper morphism to the source, bijective
on complex points, together with its algebraic projection to the target. -/
theorem exists_proper_graph_projection
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom)
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : MDifferentiable (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model Y)) (fun x => f x)) :
    ∃ (Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (p : Z ⟶ X) (q : Z ⟶ Y),
      IsReduced Z.left ∧ IsProper Z.hom ∧ IsProper p.left ∧
      Function.Bijective (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p) ∧
      ∀ z : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q z = f (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p z) := by
  obtain ⟨Z, i, hZ, hi, hproperZ, hgraph⟩ := exists_reduced_closed_graph_subscheme P Q f hf
  let : IsClosedImmersion i.left := hi
  let : Mono i := Over.mono_of_mono_left i
  let π₁ := CartesianMonoidalCategory.fst X Y
  let π₂ := CartesianMonoidalCategory.snd X Y
  let p := i ≫ π₁
  let q := i ≫ π₂
  have hproperπ : IsProper π₁.left := by dsimp [π₁]; infer_instance
  let : IsProper π₁.left := hproperπ
  have hproperp : IsProper p.left := by
    change IsProper (i.left ≫ π₁.left)
    infer_instance
  have hrel (z : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q z = f (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p z) := by
    have h := (hgraph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i z)).mp ⟨z, rfl⟩
    exact h.symm
  refine ⟨Z, p, q, hZ, hproperZ, hproperp, ⟨?_, ?_⟩, hrel⟩
  · intro z w hzw
    apply (cancel_mono i).mp
    apply CartesianMonoidalCategory.hom_ext (z ≫ i) (w ≫ i)
    · exact hzw
    · change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q z = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q w
      rw [hrel, hrel, hzw]
  · intro x
    let r : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y) := CartesianMonoidalCategory.lift x (f x)
    have hr : r ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) := by
      apply (hgraph r).mpr
      change f (r ≫ π₁) = r ≫ π₂
      simp only [r, π₁, π₂, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, ?_⟩
    change (z ≫ i) ≫ π₁ = x
    change z ≫ i = r at hz
    rw [hz]
    exact CartesianMonoidalCategory.lift_fst x (f x)

theorem exists_algebraic_map
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom)
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : MDifferentiable (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model Y)) f) :
    ∃ g : X ⟶ Y, ∀ x, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x := by
  obtain ⟨Z, p, q, hZ, hproperZ, hp, hbij, hq⟩ := exists_proper_graph_projection P Q f hf
  let : IsReduced Z.left := hZ
  let : IsProper Z.hom := hproperZ
  let : IsProper p.left := hp
  let : IsIso p.left := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteNormalIso.Constructions.Algebraization.isIso_of_proper_bijective_complex_points p hbij
  let : IsIso ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).map p) := inferInstanceAs (IsIso p.left)
  let : IsIso p := isIso_of_reflects_iso p (Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
  refine ⟨inv p ≫ q, fun x => ?_⟩
  rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, hq]
  change f ((x ≫ inv p) ≫ p) = f x
  simp

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization
