import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-! # Rational Support Units -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RationalSupportUnits

noncomputable section

/-! A nonzero rational function is represented by an actual unit at
every codimension-one point outside a finite exceptional set, including
points on nonnormal integral schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

universe u

theorem exists_finite_exceptional (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) (hf : f ≠ 0) :
    ∃ S : Finset X, (∀ x ∈ S, Order.coheight x = 1) ∧
      ∀ x : X, Order.coheight x = 1 → x ∉ S →
        ∃ a : X.presheaf.stalk x, IsUnit a ∧
          algebraMap (X.presheaf.stalk x) X.functionField a = f := by
  obtain ⟨U, _, a, hU, hfa, ha⟩ := exists_isUnit_germ_eq X f hf
  let : Nonempty U := hU
  let S := (Divisors.LineBundles.Ord.BundleCycles.finite_codimension_one_complement X U).toFinset
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    exact ((Set.Finite.mem_toFinset _).mp hx).1
  · intro x hx hxS
    have hxU : x ∈ U := by
      by_contra hn
      exact hxS ((Set.Finite.mem_toFinset _).mpr ⟨hx, hn⟩)
    refine ⟨X.presheaf.germ U x hxU a, ha.map (X.presheaf.germ U x hxU).hom, ?_⟩
    exact (X.algebraMap_germ_eq_germToFunctionField hxU a).trans hfa

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RationalSupportUnits
