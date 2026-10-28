import OAI.AlgebraicGeometry.Albanese.Construction.RefinementBound
import OAI.AlgebraicGeometry.Albanese.Construction.EtaleMono
import OAI.AlgebraicGeometry.Albanese.Construction.FiberInjective
import Mathlib.Data.Nat.Find

/-! # Maximal Refinement -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.MaximalRefinement

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- A pointed generated target refining a fixed target without changing its
dimension. All entries are actual abelian varieties and scheme morphisms. -/
structure GeneratingRefinement (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : X.toOver ⟶ B.toOver) where
  target : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  map : X.toOver ⟶ target.toOver
  projection : target.toOver ⟶ B.toOver
  pointed : x₀ ≫ map = 1
  hom : IsMonHom projection
  commutes : map ≫ projection = b
  generates : GeneratedClosed.Generates X target map
  dimension : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension target.variety.structureMap =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap

attribute [instance] GeneratingRefinement.hom

/-- A generated pointed target is a refinement of itself. -/
def GeneratingRefinement.refl (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : X.toOver ⟶ B.toOver)
    (hb0 : x₀ ≫ b = 1) (hb : GeneratedClosed.Generates X B b) : GeneratingRefinement X x₀ B b where
  target := B
  map := b
  projection := 𝟙 B.toOver
  pointed := hb0
  hom := inferInstance
  commutes := by simp
  generates := hb
  dimension := rfl

/-- The finite fiber cardinality being maximized. -/
def GeneratingRefinement.fiberCard {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    {x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver}
    {B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {b : X.toOver ⟶ B.toOver}
    (r : GeneratingRefinement X x₀ B b) (y : B.toOver.left) : ℕ :=
  Nat.card (r.projection.left.fiber y)

/-- Composing two refinements preserves generation and dimension. -/
def GeneratingRefinement.trans {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    {x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver}
    {B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {b : X.toOver ⟶ B.toOver}
    (r : GeneratingRefinement X x₀ B b)
    (s : GeneratingRefinement X x₀ r.target r.map) : GeneratingRefinement X x₀ B b where
  target := s.target
  map := s.map
  projection := s.projection ≫ r.projection
  pointed := s.pointed
  hom := inferInstance
  commutes := by rw [← Category.assoc, s.commutes, r.commutes]
  generates := s.generates
  dimension := s.dimension.trans r.dimension

/-- A refinement with maximal finite fiber cardinality exists. The bound is
proved from a fixed word fiber; no bound on isogeny degrees is assumed. -/
theorem exists_maximal_generating_refinement (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : X.toOver ⟶ B.toOver)
    (hb0 : x₀ ≫ b = 1) (hb : GeneratedClosed.Generates X B b) (y : B.toOver.left) :
    ∃ r : GeneratingRefinement X x₀ B b,
      ∀ s : GeneratingRefinement X x₀ B b, s.fiberCard y ≤ r.fiberCard y := by
  classical
  let N := RefinementBound.wordFiberComponentCount X B b y
  let P (n : ℕ) := ∃ r : GeneratingRefinement X x₀ B b, r.fiberCard y = n
  have hbound (r : GeneratingRefinement X x₀ B b) : r.fiberCard y ≤ N :=
    RefinementBound.refinement_fiber_card_bound X x₀ r.target B r.map b r.projection r.commutes
      r.generates hb r.dimension y
  let r₀ := GeneratingRefinement.refl X x₀ B b hb0 hb
  have hmax : P (Nat.findGreatest P N) :=
    Nat.findGreatest_spec (hbound r₀) ⟨r₀, rfl⟩
  obtain ⟨r, hr⟩ := hmax
  refine ⟨r, fun s => ?_⟩
  rw [hr]
  exact Nat.le_findGreatest (hbound s) ⟨s, rfl⟩

/-- A refinement maximizing the identity fiber has no further nontrivial
generated refinement of the same dimension. -/
theorem maximal_refinement_isIso (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : X.toOver ⟶ B.toOver) (hb : GeneratedClosed.Generates X B b)
    (r : GeneratingRefinement X x₀ B b)
    (hmax : ∀ s : GeneratingRefinement X x₀ B b,
      s.fiberCard (FiberInjective.identitySchemePoint B) ≤ r.fiberCard (FiberInjective.identitySchemePoint B))
    (s : GeneratingRefinement X x₀ r.target r.map) : IsIso s.projection := by
  have : Surjective s.projection.left :=
    GeneratedClosed.refinement_surjective X s.target r.target s.map r.map s.projection s.commutes r.generates
  have : Etale s.projection.left :=
    FiniteRefinements.refinement_etale X s.target r.target s.map r.map s.projection s.commutes r.generates s.dimension
  have : IsFinite s.projection.left :=
    FiniteRefinements.refinement_finite X s.target r.target s.map r.map s.projection s.commutes r.generates s.dimension
  have : IsFinite r.projection.left :=
    FiniteRefinements.refinement_finite X r.target B r.map b r.projection r.commutes hb r.dimension
  let y := FiberInjective.identitySchemePoint B
  let g := FiniteRefinements.factorFiberMap s.projection.left r.projection.left y
  have : Surjective g := FiniteRefinements.factorFiberMap_surjective s.projection.left r.projection.left y
  have hc : Nat.card ((s.projection.left ≫ r.projection.left).fiber y) ≤
      Nat.card (r.projection.left.fiber y) := hmax (r.trans s)
  have hg : Function.Injective g := (g.surjective.bijective_of_nat_card_le hc).injective
  apply EtaleMono.abelian_etale_isIso_of_point_injective s.target r.target s.projection
  exact FiberInjective.hom_point_injective_of_identity_fiber s.target r.target B s.projection r.projection hg

/-- Every pointed generated target admits an equal-dimensional generated
refinement that cannot be further refined in that dimension. -/
theorem exists_refinement_without_further_refinements (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : X.toOver ⟶ B.toOver)
    (hb0 : x₀ ≫ b = 1) (hb : GeneratedClosed.Generates X B b) :
    ∃ r : GeneratingRefinement X x₀ B b,
      ∀ s : GeneratingRefinement X x₀ r.target r.map, IsIso s.projection := by
  obtain ⟨r, hr⟩ := exists_maximal_generating_refinement X x₀ B b hb0 hb (FiberInjective.identitySchemePoint B)
  exact ⟨r, maximal_refinement_isIso X x₀ B b hb r hr⟩

end

end OAI.AlgebraicGeometry.Albanese.Construction.MaximalRefinement
