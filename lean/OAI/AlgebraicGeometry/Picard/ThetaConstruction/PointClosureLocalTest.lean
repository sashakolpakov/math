import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ClosedSupport
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ProperLocalBaseSmoothness
import Mathlib.AlgebraicGeometry.Stalk

/-! # Point Closure Local Test -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.PointClosureLocalTest.Geometric

noncomputable section

/-! The original closure of a point in a proper family gives an
integral test scheme meeting the closed local fiber. Its actual stalk
spectrum retains the same generic point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} (x : X)

def pointClosureIdeal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure ({x} : Set X), isClosed_closure⟩

def pointClosure : Scheme.{u} := (pointClosureIdeal x).subscheme
def pointClosureInclusion : pointClosure x ⟶ X := (pointClosureIdeal x).subschemeι

instance pointClosure_integral : IsIntegral (pointClosure x) :=
  PELModuli.IntegralModel.Integral.ClosedSupport.vanishingIdeal_subscheme_integral _ isIrreducible_singleton.closure

instance pointClosureInclusion_closed : IsClosedImmersion (pointClosureInclusion x) :=
  inferInstanceAs (IsClosedImmersion (pointClosureIdeal x).subschemeι)

theorem pointClosureInclusion_range : Set.range (pointClosureInclusion x) = closure ({x} : Set X) := by
  exact (Scheme.IdealSheafData.range_subschemeι (pointClosureIdeal x)).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

theorem pointClosure_generic : pointClosureInclusion x (genericPoint (pointClosure x)) = x := by
  have hx : x ∈ Set.range (pointClosureInclusion x) := by
    rw [pointClosureInclusion_range]
    exact subset_closure (Set.mem_singleton x)
  obtain ⟨y, hy⟩ := hx
  have ha : pointClosureInclusion x (genericPoint (pointClosure x)) ⤳ x :=
    ((genericPoint_specializes y).map (pointClosureInclusion x).continuous).trans (specializes_of_eq hy)
  have hb : x ⤳ pointClosureInclusion x (genericPoint (pointClosure x)) := by
    apply specializes_iff_mem_closure.mpr
    rw [← pointClosureInclusion_range]
    exact ⟨_, rfl⟩
  exact (ha.antisymm hb).eq

theorem pointClosure_meets_closed_fiber {R : Type u} [CommRing R] [IsLocalRing R]
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ y : pointClosure x, (pointClosureInclusion x ≫ f) y = IsLocalRing.closedPoint R := by
  let p := pointClosureInclusion x ≫ f
  let : IsProper p := inferInstanceAs (IsProper (pointClosureInclusion x ≫ f))
  have hc : IsClosed (Set.range p) := p.isClosedMap.isClosed_range
  have hm : IsLocalRing.closedPoint R ∈ Set.range p :=
    (IsLocalRing.specializes_closedPoint (p (genericPoint (pointClosure x)))).mem_closed hc ⟨_, rfl⟩
  exact hm

theorem integral_fromSpecStalk_generic {Y : Scheme.{u}} [IsIntegral Y] (y : Y) :
    Y.fromSpecStalk y (genericPoint (Spec (Y.presheaf.stalk y))) = genericPoint Y := by
  have hr : genericPoint Y ∈ Set.range (Y.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes y
  obtain ⟨z, hz⟩ := hr
  have h₁ : Y.fromSpecStalk y (genericPoint (Spec (Y.presheaf.stalk y))) ⤳ genericPoint Y :=
    ((genericPoint_specializes z).map (Y.fromSpecStalk y).continuous).trans (specializes_of_eq hz)
  exact (h₁.antisymm (genericPoint_specializes _)).eq

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.PointClosureLocalTest.Geometric
