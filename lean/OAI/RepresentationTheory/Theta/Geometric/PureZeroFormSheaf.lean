import OAI.RepresentationTheory.Theta.Geometric.SmoothZeroFormFunctions
import OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf

/-! # Pure Zero Form Sheaf -/

namespace OAI.RepresentationTheory.Theta.Geometric.PureZeroFormSheaf

noncomputable section

/-! The actual pure zero-form sheaf is the smooth function sheaf,
so its first cohomology vanishes on a compact complex manifold. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def smoothPureZeroFormEquiv (U : Opens M) : SmoothCocyclePrimitive.SmoothOpenScalar E U ≃+ AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E U 0 where
  toFun f := ⟨SmoothZeroFormFunctions.smoothOpenZeroFormEquiv U f, fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _⟩
  invFun a := (SmoothZeroFormFunctions.smoothOpenZeroFormEquiv U).symm a.val
  left_inv f := (SmoothZeroFormFunctions.smoothOpenZeroFormEquiv U).symm_apply_apply f
  right_inv a := Subtype.ext ((SmoothZeroFormFunctions.smoothOpenZeroFormEquiv U).apply_symm_apply a.val)
  map_add' f g := Subtype.ext ((SmoothZeroFormFunctions.smoothOpenZeroFormEquiv U).map_add f g)

def smoothPureZeroFormSheafIso :
    SmoothSheaf.smoothComplexFunctionSheaf E M ≅ AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0 :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => (smoothPureZeroFormEquiv E M U.unop).toAddCommGrpIso) (by
      intro U V h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      apply Subtype.ext
      apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
      intro x
      apply ContinuousAlternatingMap.ext
      intro v
      change AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm _ x v = (AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm f).restrict (leOfHom h.unop) x v
      rw [AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply,
        AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm_apply]
      rfl))

theorem pureZeroFormSheaf_H1_zero [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0) 1) : v = 0 := by
  let e := smoothPureZeroFormSheafIso E M
  have H := congrArg (CategoryTheory.Sheaf.H.map e.hom 1)
    (SmoothSheaf.smoothComplexFunctionSheaf_H1_zero E M (CategoryTheory.Sheaf.H.map e.inv 1 v))
  rw [← CategoryTheory.Sheaf.H.map_comp_apply, e.inv_hom_id,
    CategoryTheory.Sheaf.H.map_id_apply, map_zero] at H
  exact H

end

end OAI.RepresentationTheory.Theta.Geometric.PureZeroFormSheaf
