import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction

/-! # Section Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

noncomputable section

/-!
Iterated multiplication by a section and preservation of ratios on its
nonvanishing open. The transition maps are morphisms of the global power sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M : Y.Modules}

theorem pullbackSection_postcomp (f : X ⟶ Y) (s : Line.Bundles.structureModule Y ⟶ L) (a : L ⟶ M) :
    Ample.LineBundles.pullbackSection f (s ≫ a) = Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullback f).map a := by
  simp only [Ample.LineBundles.pullbackSection, Functor.map_comp, Category.assoc]

/-- A module map sending one local frame to another is invertible on that open. -/
theorem pullback_map_isIso_of_frames (f : X ⟶ Y)
    (s : Line.Bundles.structureModule Y ⟶ L) (s' : Line.Bundles.structureModule Y ⟶ M) (a : L ⟶ M)
    (ha : s ≫ a = s') [IsIso (Ample.LineBundles.pullbackSection f s)] [IsIso (Ample.LineBundles.pullbackSection f s')] :
    IsIso ((Scheme.Modules.pullback f).map a) := by
  have he : Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullback f).map a = Ample.LineBundles.pullbackSection f s' :=
    (pullbackSection_postcomp f s a).symm.trans (congrArg (Ample.LineBundles.pullbackSection f) ha)
  have : IsIso (Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullback f).map a) := he.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp this

/-- A map carrying the denominator frame to a new frame preserves all section ratios. -/
theorem frameCoordinate_pullback_postcomp (f : X ⟶ Y)
    (s : Line.Bundles.structureModule Y ⟶ L) (s' : Line.Bundles.structureModule Y ⟶ M) (a : L ⟶ M)
    (ha : s ≫ a = s') (t : Line.Bundles.structureModule Y ⟶ L)
    [IsIso (Ample.LineBundles.pullbackSection f s)] [IsIso (Ample.LineBundles.pullbackSection f s')] :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s') (Ample.LineBundles.pullbackSection f (t ≫ a)) =
      Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) := by
  have hi : IsIso ((Scheme.Modules.pullback f).map a) := pullback_map_isIso_of_frames f s s' a ha
  have he : Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullback f).map a = Ample.LineBundles.pullbackSection f s' :=
    (pullbackSection_postcomp f s a).symm.trans (congrArg (Ample.LineBundles.pullbackSection f) ha)
  have ht := (pullbackSection_postcomp f t a).symm
  exact (Frame.FrameRestriction.frameCoordinate_congr he ht).symm.trans
    (Frame.FrameRestriction.frameCoordinate_targetIso (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t)
      (asIso ((Scheme.Modules.pullback f).map a)))

/-- Iterated multiplication raises the power degree by the specified amount. -/
def powerSectionTransition (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) :
    (m : ℕ) → (TensorPower.PowerSheaf.tensorPowerModule L n ⟶ TensorPower.PowerSheaf.tensorPowerModule L (n + m))
  | 0 => 𝟙 _
  | m + 1 => powerSectionTransition s n m ≫ Section.PowerMultiplication.multiplyPowerBySection s (n + m)

theorem tensorPowerSection_transition (s : Line.Bundles.structureModule Y ⟶ L) (n m : ℕ) :
    TensorPower.Maps.tensorPowerSection s n ≫ SectionTransitions.powerSectionTransition s n m = TensorPower.Maps.tensorPowerSection s (n + m) := by
  induction m with
  | zero => simp only [SectionTransitions.powerSectionTransition, Nat.add_zero, Category.comp_id]
  | succ m ih =>
    change TensorPower.Maps.tensorPowerSection s n ≫ (SectionTransitions.powerSectionTransition s n m ≫ Section.PowerMultiplication.multiplyPowerBySection s (n + m)) = _
    rw [← Category.assoc, ih, Section.PowerMultiplication.tensorPowerSection_multiply]
    rfl

/-- The degree transitions are invertible wherever the original section is a frame. -/
theorem powerSectionTransition_pullback_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection f s)] (n m : ℕ) :
    IsIso ((Scheme.Modules.pullback f).map (SectionTransitions.powerSectionTransition s n m)) := by
  have : IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) := Nonvanishing.tensorPowerSection_pullback_isIso f s n
  have : IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s (n + m))) :=
    Nonvanishing.tensorPowerSection_pullback_isIso f s (n + m)
  exact pullback_map_isIso_of_frames f _ _ _ (tensorPowerSection_transition s n m)

/-- Increasing the degree of a numerator by multiplication with `s` preserves
its ratio to the corresponding power of `s` on the nonvanishing open. -/
theorem frameCoordinate_powerSectionTransition (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection f s)] (n m : ℕ)
    (t : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L n) :
    letI := Nonvanishing.tensorPowerSection_pullback_isIso f s n
    letI := Nonvanishing.tensorPowerSection_pullback_isIso f s (n + m)
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s (n + m)))
      (Ample.LineBundles.pullbackSection f (t ≫ SectionTransitions.powerSectionTransition s n m)) =
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) (Ample.LineBundles.pullbackSection f t) := by
  have : IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) := Nonvanishing.tensorPowerSection_pullback_isIso f s n
  have : IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s (n + m))) :=
    Nonvanishing.tensorPowerSection_pullback_isIso f s (n + m)
  exact frameCoordinate_pullback_postcomp f _ _ _ (tensorPowerSection_transition s n m) t

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions
