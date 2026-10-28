import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity
import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectivePresentation
import OAI.AlgebraicTopology.Products.CupCohomology
import OAI.AlgebraicGeometry.ComplexMultiplication.HomBaseChange

/-! # Intersections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Intersections.CM.SurfaceConstruction

noncomputable section

/-!
Actual intersection representatives and their cup classes. The full ProjectionFormula Chow
proposition supplies existence of representatives, rather than an unproved
moving-lemma axiom. Full ThomClass intersection compatibility identifies their
native geometric classes. This module uses smooth projective presentations,
exactly as those two committed input specifications do.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicTopology.Products.CupCohomology
open scoped TensorProduct

/-- The complete strengthened Chow statement of ProjectionFormula. -/
def ChowProjectionFormula : Prop :=
  ∀ {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (_hf : IsProper f.left) (P : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X Y)
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (p q s : ℕ) (_hdeg : q + n = s + m)
    (_hdegCup : (p + q) + n = (p + s) + m),
    ∃ (intersectionX : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ X p →ₗ[ℚ]
          IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ X q →ₗ[ℚ] IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ X (p + q))
      (intersectionY : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ Y p →ₗ[ℚ]
          IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ Y s →ₗ[ℚ] IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ Y (p + s))
      (pull : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ Y p →ₗ[ℚ] IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ X p)
      (pushQ : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ X q →ₗ[ℚ] IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ Y s)
      (pushPQ : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ X (p + q) →ₗ[ℚ]
          IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ Y (p + s)),
      (∀ a b, IntersectionTheory.ProjectionFormula.ProperCycleLinearity.chowIntersection X p q a b = {intersectionX a b}) ∧
      (∀ a b, IntersectionTheory.ProjectionFormula.ProperCycleLinearity.chowIntersection Y p s a b = {intersectionY a b}) ∧
      (∀ a, IntersectionTheory.ProjectionFormula.ProperCycleLinearity.chowPullback P f n p a = {pull a}) ∧
      (∀ b, IntersectionTheory.ProjectionFormula.ProperCycleLinearity.chowPushforward f q s b = {pushQ b}) ∧
      (∀ c, IntersectionTheory.ProjectionFormula.ProperCycleLinearity.chowPushforward f (p + q) (p + s) c = {pushPQ c}) ∧
      ∀ (α : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ Y p) (β : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ChowQ X q),
        pushPQ (intersectionX (pull α) β) = intersectionY α (pushQ β)

/-- ProjectionFormula totality yields a genuine intersection representative for every
pair of finite cycles, without assuming they already meet properly. -/
theorem exists_intersectionCycle (hProjectionFormula : ChowProjectionFormula)
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (P : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X X)
    (d : ℕ) [SmoothOfRelativeDimension d X.structureMap]
    (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ∃ c : X.RationalDimensionCycle (p + q), CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c := by
  obtain ⟨I, J, pull, pushQ, pushPQ, hI, _⟩ :=
    hProjectionFormula (𝟙 X.toOver) (IntersectionTheory.ProjectionFormula.ProperCycleLinearity.morphism_isProper _) P d d p q q rfl rfl
  obtain ⟨c, hc⟩ := IntersectionTheory.ProjectionFormula.ProperCycleLinearity.cycleToChowQ_surjective X (p + q)
    (I (IntersectionTheory.ProjectionFormula.ProperCycleLinearity.cycleToChowQ X p a) (IntersectionTheory.ProjectionFormula.ProperCycleLinearity.cycleToChowQ X q b))
  refine ⟨c, (IntersectionTheory.ProjectionFormula.ProperCycleLinearity.chowIntersection_mk_iff X p q a b c).mp ?_⟩
  rw [hI, hc]
  exact Set.mem_singleton _

/-- Choose an actual finite-cycle representative of the geometric intersection. -/
def intersectionCycle (hProjectionFormula : ChowProjectionFormula)
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (P : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X X)
    (d : ℕ) [SmoothOfRelativeDimension d X.structureMap]
    (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    X.RationalDimensionCycle (p + q) :=
  (exists_intersectionCycle hProjectionFormula X P d p q a b).choose

theorem intersectionCycle_spec (hProjectionFormula : ChowProjectionFormula)
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (P : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X X)
    (d : ℕ) [SmoothOfRelativeDimension d X.structureMap]
    (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b (intersectionCycle hProjectionFormula X P d p q a b) :=
  (exists_intersectionCycle hProjectionFormula X P d p q a b).choose_spec

def presentationDegreeCast (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {m n : ℕ} (h : m = n) :
    X.rationalCohomology m →ₗ[ℚ] X.rationalCohomology n := by
  subst n
  exact LinearMap.id

/-- Cup product with exactly the even-degree transport used by ThomClass. -/
def evenCup (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ) :
    X.rationalCohomology (p + p) →ₗ[ℚ]
      X.rationalCohomology (q + q) →ₗ[ℚ] X.rationalCohomology ((p + q) + (p + q)) :=
  (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) (p + p) (q + q)).compr₂
    (presentationDegreeCast X (add_add_add_comm p p q q))

/-- Full ThomClass intersection compatibility; the separate exterior statement
is not needed for the intersection helpers here. -/
def IntersectionCycleClassCompatibility : Prop :=
  ∀ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)),
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c →
    X.geometricCycleClassMap (p + q) c =
      evenCup X p q (X.geometricCycleClassMap p a) (X.geometricCycleClassMap q b)

theorem intersectionCycle_class (hThomClass : IntersectionCycleClassCompatibility)
    (hProjectionFormula : ChowProjectionFormula)
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (P : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X X)
    (d : ℕ) [SmoothOfRelativeDimension d X.structureMap]
    (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    X.geometricCycleClassMap (p + q) (intersectionCycle hProjectionFormula X P d p q a b) =
      evenCup X p q (X.geometricCycleClassMap p a) (X.geometricCycleClassMap q b) :=
  hThomClass X p q a b _ (intersectionCycle_spec hProjectionFormula X P d p q a b)

/-- Base change for a bilinear map with possibly different argument spaces. -/
def extendBilinear (E U V W : Type*) [Field E] [Algebra ℚ E]
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (B : U →ₗ[ℚ] V →ₗ[ℚ] W) :
    (E ⊗[ℚ] U) →ₗ[E] (E ⊗[ℚ] V) →ₗ[E] (E ⊗[ℚ] W) :=
  (ComplexMultiplication.HomBaseChange.CM.homBaseChange E V W).comp (B.baseChange E)

@[simp]
theorem extendBilinear_tmul (E U V W : Type*) [Field E] [Algebra ℚ E]
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (B : U →ₗ[ℚ] V →ₗ[ℚ] W)
    (a b : E) (u : U) (v : V) :
    extendBilinear E U V W B (a ⊗ₜ[ℚ] u) (b ⊗ₜ[ℚ] v) =
      (a * b) ⊗ₜ[ℚ] B u v := by
  simp [extendBilinear, ComplexMultiplication.HomBaseChange.CM.homBaseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

def presentationCoefficientAlgebraicClasses (E : Type*) [Field E] [Algebra ℚ E]
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Submodule E (E ⊗[ℚ] X.rationalCohomology (p + p)) :=
  LinearMap.range ((X.geometricCycleClassMap p).baseChange E)

/-- Finite coefficient cycles are closed under the actual even-degree cup
product. The proof constructs representatives term by term through ProjectionFormula. -/
theorem coefficient_evenCup_algebraic (E : Type*) [Field E] [Algebra ℚ E]
    (hThomClass : IntersectionCycleClassCompatibility) (hProjectionFormula : ChowProjectionFormula)
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (P : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X X)
    (d : ℕ) [SmoothOfRelativeDimension d X.structureMap] (p q : ℕ)
    (u : E ⊗[ℚ] X.rationalCohomology (p + p))
    (v : E ⊗[ℚ] X.rationalCohomology (q + q))
    (hu : u ∈ presentationCoefficientAlgebraicClasses E X p)
    (hv : v ∈ presentationCoefficientAlgebraicClasses E X q) :
    extendBilinear E _ _ _ (evenCup X p q) u v ∈
      presentationCoefficientAlgebraicClasses E X (p + q) := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  induction a using TensorProduct.inductionOn with
  | add a c ha hc =>
    simpa only [map_add, LinearMap.add_apply] using
      (presentationCoefficientAlgebraicClasses E X (p + q)).add_mem ha hc
  | tmul r a =>
    induction b using TensorProduct.inductionOn with
    | add b c hb hc =>
      simpa only [map_add] using
        (presentationCoefficientAlgebraicClasses E X (p + q)).add_mem hb hc
    | tmul s b =>
      refine ⟨(r * s) ⊗ₜ[ℚ] intersectionCycle hProjectionFormula X P d p q a b, ?_⟩
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, extendBilinear_tmul,
        intersectionCycle_class hThomClass hProjectionFormula]

end

end OAI.AlgebraicGeometry.HodgeConjecture.Intersections.CM.SurfaceConstruction
