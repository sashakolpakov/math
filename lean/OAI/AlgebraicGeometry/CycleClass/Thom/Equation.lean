import OAI.AlgebraicGeometry.CycleClass.Thom.ManifoldEquationCoordinates

/-! # Equation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Equation.Constructions.ThomClass

noncomputable section

/-! An actual holomorphic submersion defining an embedded zero locus
pulls the normalized complex normal class back to its canonical Thom
class. Normal coordinates and their required regularity are proved. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.ManifoldEquationCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (f : V.analyticSpace ⟶ TopCat.of (Fin p → ℂ))
  (hzero : ∀ y, y ∈ Set.range Z.regularComplementInclusion ↔ f y = 0)

include hzero in
theorem equation_mapsTo : Set.MapsTo f (Set.range Z.regularComplementInclusion)ᶜ ({0}ᶜ) :=
  fun y hy hz => hy ((hzero y).mpr hz)

theorem equation_pullback_eq_Thom
    (hf : ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hs : ∀ x : Z.regularAnalyticSpace, Function.Surjective
      (mfderiv 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin p → ℂ) f (Z.regularComplementInclusion x))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (equation_mapsTo Z f hzero)
      (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) = Z.regularThomClass := by
  classical
  have he := fun x : Z.regularAnalyticSpace => ManifoldEquationCoordinates.Constructions.exists_equation_normalPair Z f x
    (hf (Z.regularComplementInclusion x)) (hs x) ⊤ (Set.mem_univ _)
    (fun y _ => hzero y)
  choose P _ hPd hPn using he
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique Z.regularComplementInclusion Z.holomorphic
    Z.differential_injective Z.closed p Z.regularComplement_complexImmersionCodimension P hPd
  intro x
  rw [(P x).rationalClassFin_eq_normalPullback]
  let i := Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (P x).neighborhood
  have hm : i ≫ f = (P x).normalCoordinate := by
    ext y j
    exact congrFun (hPn x y).symm j
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) i f
      (A := (P x).relativeComplement) (B := (Set.range Z.regularComplementInclusion)ᶜ)
      (C := ({0}ᶜ)) (fun _ hy => hy) (equation_mapsTo Z f hzero) (2 * p))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  apply hc.trans
  have hmap : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (i ≫ f)
      (A := (P x).relativeComplement) (B := ({0}ᶜ))
      (fun y hy => equation_mapsTo Z f hzero hy) (2 * p) =
      (P x).normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) := by
    unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
    congr 1
  exact ConcreteCategory.congr_hom hmap (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Equation.Constructions.ThomClass
