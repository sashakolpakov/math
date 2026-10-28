import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.Point
import OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary

/-! # Principal Point Sum -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalPointSum.Constructions

noncomputable section

/-! The actual principal point divisor is exactly the finite sum over the
codimension-one points outside any genuine unit representative. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

local instance : Fintype (FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

theorem principalPointDivisor_eq_sum :
    Point.Constructions.rationalPrincipalPointDivisor X.left g =
      ∑ z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, Finsupp.single z.val (X.left.ord g z.val : ℚ) := by
  classical
  ext x
  rw [Point.Constructions.rationalPrincipalPointDivisor_apply, Finsupp.finsetSum_apply]
  by_cases hx : Order.coheight x = 1 ∧ x ∉ D.domain
  · let z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain := ⟨x, hx⟩
    rw [Finset.sum_eq_single z]
    · exact Finsupp.single_eq_same.symm
    · intro y _ hy
      exact Finsupp.single_eq_of_ne (fun h => hy (Subtype.ext h.symm))
    · simp
  · have ho : X.left.ord g x = 0 := by
      by_cases hc : Order.coheight x = 1
      · exact D.ord_eq_zero x (by_contra fun hn => hx ⟨hc, hn⟩)
      · exact Scheme.ord_eq_zero_of_coheight_neq_one hc g
    rw [ho, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro z _
    exact Finsupp.single_eq_of_ne (fun h => hx (h ▸ z.property))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalPointSum.Constructions
