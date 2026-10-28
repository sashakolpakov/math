import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothOpenRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.BaseOpenFactorization

/-! # Smooth Open Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothOpenClassification

noncomputable section

/-! The constructed open base exactly classifies all base changes making a proper flat finitely presented family smooth. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem smooth_recovery_iff_range_subset_properSmoothBaseOpen
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (h : IsPullback q p f c) :
    Smooth p ↔ Set.range c ⊆ SmoothBaseOpen.properSmoothBaseOpen f := by
  constructor
  · intro hp
    have : Smooth p := hp
    exact SmoothOpenRecovery.smooth_recovery_range_subset_properSmoothBaseOpen q p f c h
  · intro hc
    have : Smooth (f ∣_ SmoothBaseOpen.properSmoothBaseOpen f) := SmoothBaseOpen.properSmoothBaseOpen_restrict_smooth f
    exact HilbertConstruction.Smooth.BaseOpenFactorization.smooth_recovery_of_range_subset_open q p f c h (SmoothBaseOpen.properSmoothBaseOpen f) hc

theorem smooth_pullback_iff_range_subset_properSmoothBaseOpen
    {X S T : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (c : T ⟶ S) : Smooth (pullback.snd f c) ↔ Set.range c ⊆ SmoothBaseOpen.properSmoothBaseOpen f :=
  smooth_recovery_iff_range_subset_properSmoothBaseOpen _ _ f c (IsPullback.of_hasPullback f c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothOpenClassification
