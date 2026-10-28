import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Support Fractions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportFractions

noncomputable section

/-! A support rational function has a numerator and denominator
lifted from every ambient affine chart meeting the support. The same
sections represent it at every support point in that chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction

theorem exists_sections (X : Scheme) (W : IrreducibleCloseds X)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    ∃ a b : Γ(X, U), (CycleClass.Geometric.GenericPoint.reducedSupportι W).app U a ≠ 0 ∧ (CycleClass.Geometric.GenericPoint.reducedSupportι W).app U b ≠ 0 ∧
      ∀ (x : X) (hxW : x ∈ (W : Set X)) (hxU : x ∈ U),
        Support.LocalFraction.Restriction.toFunctionField X W x hxW (X.presheaf.germ U x hxU a) ≠ 0 ∧
        Support.LocalFraction.Restriction.toFunctionField X W x hxW (X.presheaf.germ U x hxU b) ≠ 0 ∧
        g = Support.LocalFraction.Restriction.toFunctionField X W x hxW (X.presheaf.germ U x hxU a) /
          Support.LocalFraction.Restriction.toFunctionField X W x hxW (X.presheaf.germ U x hxU b) := by
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let V := (CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U
  let A := Γ(Y, V)
  let : IsFractionRing A Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y V (hU.preimage (CycleClass.Geometric.GenericPoint.reducedSupportι W))
  obtain ⟨c, d, hd, hfrac⟩ := IsFractionRing.div_surjective A g
  have hd₀ : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hc₀ : c ≠ 0 := by
    intro h
    exact hg (by rw [← hfrac, h, map_zero, zero_div])
  obtain ⟨a, ha⟩ := (CycleClass.Geometric.GenericPoint.reducedSupportι W).app_surjective U hU c
  obtain ⟨b, hb⟩ := (CycleClass.Geometric.GenericPoint.reducedSupportι W).app_surjective U hU d
  refine ⟨a, b, (ha ▸ hc₀), (hb ▸ hd₀), ?_⟩
  intro x hxW hxU
  have hfa : Support.LocalFraction.Restriction.toFunctionField X W x hxW (X.presheaf.germ U x hxU a) = algebraMap A Y.functionField c := by
    rw [Support.LocalFraction.Restriction.toFunctionField_germ X W U x hxW hxU a, ha]
    rfl
  have hfb : Support.LocalFraction.Restriction.toFunctionField X W x hxW (X.presheaf.germ U x hxU b) = algebraMap A Y.functionField d := by
    rw [Support.LocalFraction.Restriction.toFunctionField_germ X W U x hxW hxU b, hb]
    rfl
  rw [hfa, hfb]
  exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective A Y.functionField)).mpr hc₀,
    (map_ne_zero_iff _ (IsFractionRing.injective A Y.functionField)).mpr hd₀, hfrac.symm⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportFractions
