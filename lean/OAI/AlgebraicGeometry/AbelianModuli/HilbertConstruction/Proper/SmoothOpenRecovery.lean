import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothBaseOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberPointCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredSmoothFibers

/-! # Smooth Open Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothOpenRecovery

noncomputable section

/-! Every base change that makes a proper flat finitely presented family smooth lands in the constructed smooth base open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem mem_properSmoothBaseOpen_of_smooth_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (s : S) [Smooth (f.fiberToSpecResidueField s)] : s ∈ SmoothBaseOpen.properSmoothBaseOpen f := by
  rintro ⟨x, hx, hxs⟩
  exact hx (HilbertConstruction.Smooth.FiberPointCriterion.fiber_smoothLocus_of_smooth_fiber f s x hxs)

theorem smooth_recovery_range_subset_properSmoothBaseOpen
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : IsPullback q p f c) [Smooth p] : Set.range c ⊆ SmoothBaseOpen.properSmoothBaseOpen f := by
  rintro s ⟨t, rfl⟩
  have : Smooth (f.fiberToSpecResidueField (c t)) := RecoveredSmoothFibers.smooth_fiber_of_smooth_baseChange q p f c h t
  exact mem_properSmoothBaseOpen_of_smooth_fiber f (c t)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothOpenRecovery
