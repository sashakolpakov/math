import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Power Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus

noncomputable section

/-! The nonvanishing open of a line-bundle section is unchanged by any positive tensor power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M : Y.Modules}

/-- The canonical restriction comparison transports invertibility in both directions. -/
theorem isIso_tensorPowerMap_restrict_iff (f : X ⟶ Y) [IsOpenImmersion f]
    (a : L ⟶ M) (n : ℕ) :
    IsIso (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n) ↔
      IsIso ((Scheme.Modules.restrictFunctor f).map (TensorPower.Maps.tensorPowerMap a n)) := by
  have h := congrArg (fun z => IsIso z) (TensorPower.RestrictionMaps.tensorPowerRestrictIso_naturality (n := n) f a)
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using h.to_iff

/-- A section frame restricts to any smaller open subscheme. -/
theorem pullbackSection_isIso_of_le {U V : Y.Opens} (h : V ≤ U)
    (s : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] :
    IsIso (Ample.LineBundles.pullbackSection V.ι s) := by
  have ht : IsIso (Ample.LineBundles.pullbackSection (Y.homOfLE h ≫ U.ι) s) :=
    (Nonvanishing.isIso_pullbackSection_comp_iff U.ι (Y.homOfLE h) s).mp inferInstance
  exact (congrArg (fun a : V.toScheme ⟶ Y => IsIso (Ample.LineBundles.pullbackSection a s))
    (Y.homOfLE_ι h)).mp ht

/-- A frame of a positive section power forces the section itself to be a frame
on every open where its line bundle is trivialized. -/
theorem section_isIso_of_tensorPowerSection {L : Line.Bundles.LineBundle Y}
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (n : ℕ) (hn : 0 < n) (U : Y.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L.sheaf ≅ Line.Bundles.structureModule U.toScheme)
    [IsIso (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n))] :
    IsIso (Ample.LineBundles.pullbackSection U.ι s) := by
  have hsp : IsIso ((Scheme.Modules.pullback U.ι).map (TensorPower.Maps.tensorPowerSection s n)) :=
    (Nonvanishing.isIso_pullbackSection_iff U.ι _).mp inferInstance
  have hp : IsIso ((Scheme.Modules.pullback U.ι).map (TensorPower.Maps.tensorPowerMap s n)) := by
    simpa only [TensorPower.Maps.tensorPowerSection, Functor.map_comp, isIso_comp_left_iff] using hsp
  have hr : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (TensorPower.Maps.tensorPowerMap s n)) :=
    (Power.Nonvanishing.isIso_restrict_map_iff U.ι _).mpr hp
  have : IsIso (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor U.ι).map s) n) :=
    (isIso_tensorPowerMap_restrict_iff U.ι s n).mpr hr
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map s) :=
    TensorPower.Units.isIso_of_tensorPowerMap_of_frames _ n hn
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (Line.Bundles.structureModule Y) ≪≫
        Line.Bundles.structureModulePullbackIso U.ι)
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e)
  exact (Nonvanishing.isIso_pullbackSection_iff U.ι s).mpr ((Power.Nonvanishing.isIso_restrict_map_iff U.ι s).mp this)

/-- Positive powers have exactly the same nonvanishing open as the original line-bundle section. -/
theorem sectionNonvanishing_tensorPowerSection {L : Line.Bundles.LineBundle Y}
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (n : ℕ) (hn : 0 < n) :
    Ample.LineBundles.sectionNonvanishing (TensorPower.Maps.tensorPowerSection s n) = Ample.LineBundles.sectionNonvanishing s := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    change Y.Opens at U
    have : IsIso (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n)) := hU
    obtain ⟨V, hxV, ⟨e⟩⟩ := L.locallyTrivial x
    have : IsIso (Ample.LineBundles.pullbackSection (U ⊓ V).ι (TensorPower.Maps.tensorPowerSection s n)) :=
      pullbackSection_isIso_of_le inf_le_left (TensorPower.Maps.tensorPowerSection s n)
    have hs : IsIso (Ample.LineBundles.pullbackSection (U ⊓ V).ι s) :=
      section_isIso_of_tensorPowerSection s n hn (U ⊓ V) (L.frameRestrict inf_le_right e)
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨U ⊓ V, hs, ⟨hxU, hxV⟩⟩
  · exact Power.Nonvanishing.sectionNonvanishing_le_tensorPowerSection s n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus
