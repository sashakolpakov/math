import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction

/-! # Point Support Meeting -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PointSupportMeeting.BundleCycles

noncomputable section

/-! A support meeting an analytic open inside an algebraic open has its literal generic point in that algebraic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction

variable (N : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType N.hom]

omit [LocallyOfFiniteType N.hom] in
theorem schemePoint_mem_open_of_support_meeting (x : N.left) (B : N.left.Opens)
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen N B)
    (hx : ∃ y : U, y.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (irreducibleSetEquivPoints.symm x))) :
    x ∈ B := by
  obtain ⟨y, hy⟩ := hx
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range] at hy
  have hz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ closure ({x} : Set N.left) := hy
  exact (specializes_iff_mem_closure.mpr hz).mem_open B.isOpen (hU y.property)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PointSupportMeeting.BundleCycles
