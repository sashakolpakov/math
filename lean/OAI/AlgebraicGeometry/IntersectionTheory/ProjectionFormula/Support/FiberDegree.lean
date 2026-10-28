import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleFiberDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.FiberDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.EtaleRestriction

/-! # Fiber Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FiberDegree

noncomputable section

/-! The fiber weights of a proper integral support map add to its
native generic degree on the finite etale target open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (W : IrreducibleCloseds X.carrier) (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens)
  [Etale (U.ι ≫ Map.supportImageMap f W)] (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W))
  (hy : y ∈ Proper.EtaleRestriction.good (Map.supportImageMap f W) U)

include hy in
theorem finite : ((Map.supportImageMap f W) ⁻¹' {y}).Finite := by
  let u := Map.supportImageMap f W
  let V := Proper.EtaleRestriction.good u U
  let : IsFinite (u ∣_ V) := Proper.EtaleRestriction.finite u U
  let y' : V.toScheme := ⟨y, hy⟩
  let : Finite ((u ∣_ V) ⁻¹' ({y'} : Set V.toScheme)) := (u ∣_ V).finite_preimage_singleton y' |>.to_subtype
  let : Finite (u ⁻¹' {y}) := Finite.of_equiv _ (Open.FiberDegree.equiv u V y')
  exact Set.toFinite _

include hy in
theorem sum [Fintype ((Map.supportImageMap f W) ⁻¹' {y})] :
    ∑ x : (Map.supportImageMap f W) ⁻¹' {y}, f.left.residueDegree (CycleClass.Geometric.GenericPoint.reducedSupportι W x.val) =
      f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W) := by
  let u := Map.supportImageMap f W
  let V := Proper.EtaleRestriction.good u U
  let : IsFinite (u ∣_ V) := Proper.EtaleRestriction.finite u U
  let : Etale (u ∣_ V) := Proper.EtaleRestriction.etale u U
  let y' : V.toScheme := ⟨y, hy⟩
  let : Nonempty V := ⟨y'⟩
  obtain ⟨x, hx⟩ := Map.supportImageMap_surjective f W y
  let : Nonempty (u ⁻¹ᵁ V) := ⟨⟨x, by change u x ∈ V; rw [show u x = y from hx]; exact hy⟩⟩
  let : Fintype ((u ∣_ V) ⁻¹' ({y'} : Set V.toScheme)) :=
    Fintype.ofEquiv (u ⁻¹' {y}) (Open.FiberDegree.equiv u V y').symm
  calc
    _ = ∑ x : u ⁻¹' {y}, u.residueDegree x.val :=
      Finset.sum_congr rfl (fun x _ => (Map.supportImageMap_residueDegree f W x.val).symm)
    _ = ∑ x : (u ∣_ V) ⁻¹' ({y'} : Set V.toScheme), (u ∣_ V).residueDegree x.val :=
      (Open.FiberDegree.sum u V y').symm
    _ = (u ∣_ V).residueDegree (genericPoint (u ⁻¹ᵁ V).toScheme) :=
      ProjectionFormula.Finite.EtaleFiberDegree.sum (u ∣_ V) y'
    _ = u.residueDegree (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) := Open.FiberDegree.generic_degree u V
    _ = _ := Map.supportImageMap_generic_residueDegree f W

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FiberDegree
