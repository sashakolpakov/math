import OAI.AlgebraicGeometry.CycleClass.Thom.Betti
import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular

/-! # Component Restriction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.Class

/-! The actual component restrictions of geometric single-support classes
and of the projection-pullback cup product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Betti.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem geometricClass_single_component_same (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (C : irreducibleComponents X.carrier) (A : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) (r : ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C)
      (X.geometricCycleClassMap p (Finsupp.single ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩) r)) =
      r • A.geometricCycleClass := by
  rw [← X.componentBettiEquiv_apply, X.componentBettiEquiv_geometricCycleClassMap,
    X.componentDimensionCycleEquiv_single_same, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single]

theorem geometricClass_single_component_ne (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (C D : irreducibleComponents X.carrier) (A : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p)
    (r : ℚ) (hCD : C ≠ D) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver D)
      (X.geometricCycleClassMap p (Finsupp.single ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩) r)) = 0 := by
  rw [← X.componentBettiEquiv_apply, X.componentBettiEquiv_geometricCycleClassMap,
    X.componentDimensionCycleEquiv_single_ne p C D A r hCD, map_zero]

theorem rationalBetti_comp_apply {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (a : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Z n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n (f ≫ g) a =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n g a) := by
  simp only [Betti.Scheme.schemeBettiMap, Functor.map_comp, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp, ConcreteCategory.comp_apply]

theorem rationalBetti_cast {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) {m n : ℕ} (h : m = n)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y m) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f
      (cast (congrArg (fun k => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y k : Type)) h) a) =
      cast (congrArg (fun k => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X k : Type)) h)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) m f a) := by
  subst n
  rfl

theorem rationalBetti_cup {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p q : ℕ)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y p) (b : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y q) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + q) f (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace Y) p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X) p q
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) p f a) (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) q f b) :=
  AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) p q a b

variable (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (C : irreducibleComponents X.carrier) (D : irreducibleComponents Y.carrier)
  (Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)

local notation "E" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.productComponent X Y C D Z πX πY hprod

theorem exteriorBettiBilinear_restrict_components
    (a : X.rationalCohomology (p + p)) (b : Y.rationalCohomology (q + q)) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) ((p + q) + (p + q)) (Z.componentInclusionOver E)
      (Betti.Constructions.exteriorBettiBilinear X Y Z πX πY p q a b) =
    Betti.Constructions.exteriorBettiBilinear (X.componentVariety C).presentation (Y.componentVariety D).presentation
      (Z.componentVariety E).presentation
      (ComponentProduct.Constructions.Projections.productComponentFst X Y C D Z πX πY hprod) (ComponentProduct.Constructions.Projections.productComponentSnd X Y C D Z πX πY hprod) p q
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C) a)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) (Y.componentInclusionOver D) b) := by
  rw [Betti.Constructions.exteriorBettiBilinear_apply, Betti.Constructions.exteriorBettiBilinear_apply,
    rationalBetti_cast (Z.componentInclusionOver E) (add_add_add_comm p p q q), rationalBetti_cup,
    ← rationalBetti_comp_apply, ← rationalBetti_comp_apply,
    ← ComponentProduct.Constructions.Projections.productComponentFst_inclusion, ← ComponentProduct.Constructions.Projections.productComponentSnd_inclusion,
    rationalBetti_comp_apply, rationalBetti_comp_apply]

end AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.Class

namespace AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.IntersectionBettiBilinear

/-! The original cohomological intersection cup, with its exact ThomClass
degree transport and actual restriction to integral components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Betti.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def intersectionBettiBilinear (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ) :
    X.rationalCohomology (p + p) →ₗ[ℚ] X.rationalCohomology (q + q) →ₗ[ℚ]
      X.rationalCohomology ((p + q) + (p + q)) :=
  (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) (p + p) (q + q)).compr₂
    (Betti.Constructions.degreeTransport X (add_add_add_comm p p q q))

theorem intersectionBettiBilinear_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.rationalCohomology (p + p)) (b : X.rationalCohomology (q + q)) :
    intersectionBettiBilinear X p q a b =
      cast (congrArg (fun n => (X.rationalCohomology n : Type)) (add_add_add_comm p p q q))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) (p + p) (q + q) a b) :=
  Betti.Constructions.degreeTransport_apply X (add_add_add_comm p p q q) _

theorem intersectionBettiBilinear_restrict (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (a : X.rationalCohomology (p + p)) (b : X.rationalCohomology (q + q)) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) ((p + q) + (p + q)) (X.componentInclusionOver C)
      (intersectionBettiBilinear X p q a b) =
    intersectionBettiBilinear (X.componentVariety C).presentation p q
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C) a)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) (X.componentInclusionOver C) b) := by
  rw [intersectionBettiBilinear_apply, intersectionBettiBilinear_apply,
    Class.rationalBetti_cast (X.componentInclusionOver C) (add_add_add_comm p p q q), Class.rationalBetti_cup]

end AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.IntersectionBettiBilinear

end

end OAI
