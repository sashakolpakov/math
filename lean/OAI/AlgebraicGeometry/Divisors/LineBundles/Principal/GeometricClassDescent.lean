import OAI.AlgebraicGeometry.Divisors.LineBundles.Chow
import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDescent

/-! # Geometric Class Descent -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.GeometricClassDescent.BundleCycles

noncomputable section

/-! LineBundleCycles's full point-cycle principal relations have exactly the
coefficients in the proved normalization-based geometric descent theorem. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem principalDivisorCycle_geometric_coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (Z : IrreducibleCloseds X.carrier) :
    Chow.BundleCycles.principalDivisorCycle X W g (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X W g Z := by
  by_cases hx : CycleClass.Thom.IntersectionGeometry.supportPoint Z ∈ (W : Set X.carrier)
  · let x := CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint Z) hx
    have hxi : CycleClass.Geometric.GenericPoint.reducedSupportι W x = CycleClass.Thom.IntersectionGeometry.supportPoint Z := CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ hx
    calc
      Chow.BundleCycles.principalDivisorCycle X W g (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = Chow.BundleCycles.principalDivisorCycle X W g (CycleClass.Geometric.GenericPoint.reducedSupportι W x) :=
        congrArg (Chow.BundleCycles.principalDivisorCycle X W g) hxi.symm
      _ = ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord g x : ℚ) := by
        rw [Chow.BundleCycles.principalDivisorCycle_apply, Chow.BundleCycles.principalDivisorCoefficients_at_support]
      _ = CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X W g Z :=
        (CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient_at_image X W g Z x hxi).symm
  · rw [Chow.BundleCycles.principalDivisorCycle_apply, Chow.BundleCycles.principalDivisorCoefficients_off_support X W g _ hx]
    exact (show CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X W g Z = 0 by
      simp only [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hx]).symm

theorem isPrincipalDivisorQ_geometric_relation (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) (hz : Chow.BundleCycles.IsPrincipalDivisorQ X p z) : CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X p z := by
  obtain ⟨W, hW, g, hg, he⟩ := hz
  refine ⟨W, hW, g, hg, ?_⟩
  intro Z
  have h := congrArg (fun w : X.carrier →₀ ℚ => w (Chow.BundleCycles.cyclePointEmbedding X p Z)) he
  rw [Chow.BundleCycles.pointCycle_apply] at h
  exact h.trans (principalDivisorCycle_geometric_coefficient X W g Z.val)

theorem isPrincipalDivisorQ_geometricClass_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) (hz : Chow.BundleCycles.IsPrincipalDivisorQ X p z) : X.geometricCycleClassMap p z = 0 :=
  CycleClass.Thom.PrincipalDescent.Constructions.isPrincipalDivisor_geometricClass_zero X p z
    (isPrincipalDivisorQ_geometric_relation X p z hz)

theorem rationalEquivalenceQ_geometricClass_ker (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Chow.BundleCycles.rationalEquivalenceQ X p ≤ LinearMap.ker (X.geometricCycleClassMap p) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact isPrincipalDivisorQ_geometricClass_zero X p z hz

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.GeometricClassDescent.BundleCycles
