import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Chart Germ Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermMap.AnalyticLocal

noncomputable section

/-! Actual algebraic function evaluation in an affine regular chart,
as a map into its holomorphic germ ring. -/

open Set Filter
open scoped _root_.Topology ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

variable {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}

def affineChartGermMap (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    A →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) where
  toFun a := ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction (e x) (fun z => e.symm z a) e.open_target (e.map_source hx)
    ((he.1 a).differentiableOn (by simp))
  map_zero' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => map_zero (e.symm z))
  map_one' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => map_one (e.symm z))
  map_add' a b := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => map_add (e.symm z) a b)
  map_mul' a b := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => map_mul (e.symm z) a b)

theorem affineChartGermMap_val (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) (a : A) :
    (affineChartGermMap e he x hx a).val =
      ((fun z => e.symm z a) : Germ (𝓝 (e x)) ℂ) := rfl

theorem affineChartGermMap_value (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) (a : A) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom (e x) (affineChartGermMap e he x hx a) = x a := by
  change e.symm (e x) a = x a
  rw [e.left_inv hx]

def affineChartGermAlgHom (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    A →ₐ[ℂ] ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) where
  __ := affineChartGermMap e he x hx
  commutes' c := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => (e.symm z).commutes c)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermMap.AnalyticLocal
