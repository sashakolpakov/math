import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.ModuleSquare
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SmoothSectionGeometry

/-! # Section Support Module -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SectionSupportModule

noncomputable section

/-! A closed section identifies the actual reduced support modules
of every cycle with the restrictions of their image support modules. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (s : Y.toOver ⟶ X.toOver)
  [IsClosedImmersion s.left] (f : X.toOver ⟶ Y.toOver) (hs : s ≫ f = 𝟙 Y.toOver)
  (B : IrreducibleCloseds Y.carrier)

instance imageMap_isIso : IsIso (Support.Map.supportImageMap s B) := by
  let : IsClosedImmersion (Support.Map.algebraicMap s) := inferInstanceAs (IsClosedImmersion s.left)
  unfold Support.Map.supportImageMap
  apply IsClosedImmersion.isIso_lift
  change (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (ProperCycleLinearity.imageSupport s B)).subschemeι.ker = _
  rw [Scheme.IdealSheafData.ker_subschemeι, Support.Map.supportMap_kernel]

def inverse : CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport s B) ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme B :=
  inv (Support.Map.supportImageMap s B)

instance : IsIso (inverse s B) := by unfold inverse; infer_instance

include hs in
theorem square : CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport s B) ≫ f.left = inverse s B ≫ CycleClass.Geometric.GenericPoint.reducedSupportι B := by
  apply (cancel_epi (Support.Map.supportImageMap s B)).mp
  rw [← Category.assoc, Support.Map.supportImageMap_inclusion, Category.assoc]
  change CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ (s ≫ f).left = _
  rw [hs]
  simp [inverse]

include hs in
omit [IsClosedImmersion s.left] in
theorem mem (x : X.carrier) (hx : x ∈ (ProperCycleLinearity.imageSupport s B : Set X.carrier)) :
    f.left x ∈ (B : Set Y.carrier) := by
  rw [ProperCycleLinearity.imageSupport_eq_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [Smooth.SmoothSectionGeometry.point s f hs]

def equiv (x : X.carrier) (hx : x ∈ (ProperCycleLinearity.imageSupport s B : Set X.carrier)) :
    CycleClass.Thom.IntersectionGeometry.localSupportModule Y.carrier B (f.left x) (mem s f hs B x hx) ≃ₗ[Y.carrier.presheaf.stalk (f.left x)]
      (ModuleCat.restrictScalars (f.left.stalkMap x).hom).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier (ProperCycleLinearity.imageSupport s B) x hx) :=
  Support.ModuleSquare.equiv f.left (ProperCycleLinearity.imageSupport s B) B (inverse s B) (square s f hs B)
    x hx (mem s f hs B x hx)

include hs in
theorem residueDegree (x : X.carrier) (hx : x ∈ Set.range s.left) : f.left.residueDegree x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  have h := CyclePushforward.residueDegree_comp s.left f.left y
  rw [Principal.ClosedSectionCycle.residueDegree_immersion s.left y, mul_one] at h
  have he : s.left ≫ f.left = 𝟙 Y.carrier := congrArg Over.Hom.left hs
  rw [he] at h
  exact h.symm.trans (Scheme.Hom.residueDegree_id (show Y.carrier from y))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SectionSupportModule
