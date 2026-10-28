import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing

/-! # Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing

noncomputable section

/-! A section that locally frames a line bundle also frames each of its tensor powers there. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M : Y.Modules}

/-- The restriction and pullback functors give the same local invertibility condition. -/
theorem isIso_restrict_map_iff (f : X ⟶ Y) [IsOpenImmersion f] (a : L ⟶ M) :
    IsIso ((Scheme.Modules.restrictFunctor f).map a) ↔
      IsIso ((Scheme.Modules.pullback f).map a) := by
  have h := congrArg (fun z => IsIso z) ((Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality a)
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using h.to_iff

/-- Local invertibility of a module morphism implies local invertibility of its tensor power. -/
theorem tensorPowerMap_pullback_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (a : L ⟶ M) (n : ℕ) [IsIso ((Scheme.Modules.pullback f).map a)] :
    IsIso ((Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerMap a n)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor f).map a) :=
    (isIso_restrict_map_iff f a).mpr inferInstance
  exact (isIso_restrict_map_iff f (TensorPower.Maps.tensorPowerMap a n)).mp (TensorPower.RestrictionMaps.tensorPowerMap_restrict_isIso f a)

/-- A frame on an open subscheme raises to a frame on that same open. -/
theorem tensorPowerSection_pullback_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) [IsIso (Ample.LineBundles.pullbackSection f s)] :
    IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) := by
  have : IsIso ((Scheme.Modules.pullback f).map s) :=
    (Section.Nonvanishing.isIso_pullbackSection_iff f s).mp inferInstance
  have : IsIso ((Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerMap s n)) :=
    tensorPowerMap_pullback_isIso f s n
  apply (Section.Nonvanishing.isIso_pullbackSection_iff f (TensorPower.Maps.tensorPowerSection s n)).mpr
  simp only [TensorPower.Maps.tensorPowerSection, Functor.map_comp]
  infer_instance

/-- Taking a section to a tensor power preserves every point where it already generates. -/
theorem sectionNonvanishing_le_tensorPowerSection (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) :
    Ample.LineBundles.sectionNonvanishing s ≤ Ample.LineBundles.sectionNonvanishing (TensorPower.Maps.tensorPowerSection s n) := by
  apply sSup_le
  intro U hU
  have : IsIso (Ample.LineBundles.pullbackSection U.ι s) := hU
  apply le_sSup
  exact tensorPowerSection_pullback_isIso U.ι s n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
