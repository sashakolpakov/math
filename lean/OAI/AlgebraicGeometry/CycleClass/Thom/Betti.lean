import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectivePresentation
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Betti -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Betti.Constructions

noncomputable section

/-!
# ThomClass proof development

This file imports the checked geometric constructors, never the statement
stubs. The finite-cycle reductions below retain the actual cycle-class map
and the actual pullback/cup products. They isolate the irreducible-support
case; they do not assert that this remaining geometric case is proved.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped BigOperators

open OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry

/-- Degree transport in the actual rational cohomology family, as a linear map. -/
def degreeTransport (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {m n : ℕ} (h : m = n) :
    X.rationalCohomology m →ₗ[ℚ] X.rationalCohomology n := by
  subst n
  exact LinearMap.id

theorem degreeTransport_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {m n : ℕ}
    (h : m = n) (a : X.rationalCohomology m) :
    degreeTransport X h a =
      cast (congrArg (fun k => (X.rationalCohomology k : Type)) h) a := by
  subst n
  rfl

/-- Bilinear extension of the geometric products of integral supports. -/
def exteriorCycleBilinear
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (p q : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ]
      Y.RationalDimensionCycle q →ₗ[ℚ] Z.RationalDimensionCycle (p + q) :=
  Finsupp.linearCombination ℚ (fun A : X.DimensionCycleSupport p =>
    Finsupp.linearCombination ℚ (fun B : Y.DimensionCycleSupport q =>
      IntersectionGeometry.reducedClosedCycle Z (p + q) (IntersectionGeometry.productClosedSupport X Y Z πX πY A.val B.val)))

theorem exteriorCycleBilinear_apply
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : Y.RationalDimensionCycle q) :
    exteriorCycleBilinear X Y Z πX πY p q a b =
      IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q a b := by
  simp only [exteriorCycleBilinear, IntersectionGeometry.exteriorCycleProduct, Finsupp.linearCombination_apply,
    Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]

/-- The cohomological exterior product with the same degree transport as ThomClass. -/
def exteriorBettiBilinear
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (p q : ℕ) :
    X.rationalCohomology (p + p) →ₗ[ℚ]
      Y.rationalCohomology (q + q) →ₗ[ℚ]
        Z.rationalCohomology ((p + q) + (p + q)) :=
  ((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ)
      (Betti.Scheme.schemePointSpace Z.toOver) (p + p) (q + q)).compr₂
      (degreeTransport Z (add_add_add_comm p p q q))).compl₁₂
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πX).hom
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) πY).hom

theorem exteriorBettiBilinear_apply
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (p q : ℕ) (a : X.rationalCohomology (p + p))
    (b : Y.rationalCohomology (q + q)) :
    exteriorBettiBilinear X Y Z πX πY p q a b =
      cast (congrArg (fun k => (Z.rationalCohomology k : Type))
        (add_add_add_comm p p q q))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ)
          (Betti.Scheme.schemePointSpace Z.toOver) (p + p) (q + q)
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πX a)
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) πY b)) := by
  exact degreeTransport_apply Z (add_add_add_comm p p q q) _

/-- Bilinear maps on finite rational cycles are determined by unit supports. -/
theorem bilinear_eq_of_single_one
    {ι κ M : Type} [AddCommGroup M] [Module ℚ M]
    (F G : (ι →₀ ℚ) →ₗ[ℚ] (κ →₀ ℚ) →ₗ[ℚ] M)
    (h : ∀ A B, F (Finsupp.single A 1) (Finsupp.single B 1) =
      G (Finsupp.single A 1) (Finsupp.single B 1)) : F = G := by
  apply Finsupp.lhom_ext
  intro A r
  apply Finsupp.lhom_ext
  intro B s
  have hr : Finsupp.single A r = r • Finsupp.single A (1 : ℚ) := by simp
  have hs : Finsupp.single B s = s • Finsupp.single B (1 : ℚ) := by simp
  simp only [hr, hs, map_smul, LinearMap.smul_apply, h]

/-- Exterior compatibility for all cycles is equivalent to the genuine
 geometric statement for every pair of irreducible supports. -/
theorem exterior_compatibility_iff_supports
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ) :
    (∀ (a : X.RationalDimensionCycle p) (b : Y.RationalDimensionCycle q),
      Z.geometricCycleClassMap (p + q)
          (IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q a b) =
        exteriorBettiBilinear X Y Z πX πY p q
          (X.geometricCycleClassMap p a) (Y.geometricCycleClassMap q b)) ↔
    (∀ (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport q),
      Z.geometricCycleClassMap (p + q)
          (IntersectionGeometry.reducedClosedCycle Z (p + q)
            (IntersectionGeometry.productClosedSupport X Y Z πX πY A.val B.val)) =
        exteriorBettiBilinear X Y Z πX πY p q
          (X.geometricCycleClassMap p (Finsupp.single A 1))
          (Y.geometricCycleClassMap q (Finsupp.single B 1))) := by
  constructor
  · intro h A B
    simpa only [IntersectionGeometry.exteriorCycleProduct_single, one_mul, one_smul] using
      h (Finsupp.single A 1) (Finsupp.single B 1)
  · intro h
    let F := (exteriorCycleBilinear X Y Z πX πY p q).compr₂
      (Z.geometricCycleClassMap (p + q))
    let G := (exteriorBettiBilinear X Y Z πX πY p q).compl₁₂
      (X.geometricCycleClassMap p) (Y.geometricCycleClassMap q)
    have hFG : F = G := by
      apply bilinear_eq_of_single_one
      intro A B
      simpa only [F, G, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
        exteriorCycleBilinear_apply X Y Z πX πY hprod,
        IntersectionGeometry.exteriorCycleProduct_single, one_mul, one_smul] using h A B
    intro a b
    have he := congrArg (fun L => L a b) hFG
    simpa only [F, G, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      exteriorCycleBilinear_apply X Y Z πX πY hprod] using he

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Betti.Constructions
