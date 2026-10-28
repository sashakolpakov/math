import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrincipalCoefficients
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PointSupportMeeting

/-! # Fiber Meeting -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.FiberMeeting.BundleCycles

noncomputable section

/-! The affine inverse-image source chart contains every algebraic point over every cycle support meeting its retained analytic base open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} (k : S ⟶ N) [IsFinite k.left] (B : N.left.Opens)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B)))

include hU in
omit [IsFinite k.left] in
theorem finiteAffineChart_covers_meeting_supports (n : ℕ)
    (D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint N.hom n)
    (hD : ∃ x : U, x.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (irreducibleSetEquivPoints.symm D.val))) :
    ∀ y : S.left, k.left y = D.val → y ∈ Set.range (OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left := by
  apply PrincipalCoefficients.BundleCycles.finiteAffineChart_algebraic_fiber_cover k B D.val
  apply Scheme.PointSupportMeeting.BundleCycles.schemePoint_mem_open_of_support_meeting N D.val B U _ hD
  intro x hx
  exact (Set.ext_iff.mp (OpenChart.BundleCycles.finiteAffineBaseInclusion_analytic_range B) x).mp (hU hx)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.FiberMeeting.BundleCycles
