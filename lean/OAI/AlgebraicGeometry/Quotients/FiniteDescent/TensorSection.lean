import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus

/-! # Tensor Section -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus

noncomputable section

/-! The nonvanishing locus of a tensor product of line-bundle sections is their intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus

universe u

variable {X : Scheme.{u}} {L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
variable (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M.sheaf)

theorem isIso_on_open_iff (U : X.Opens) :
    IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t)) ↔
      IsIso (BinaryTensorId.Construction.BinaryTensorMap.map ((Scheme.Modules.restrictFunctor U.ι).map s)
        ((Scheme.Modules.restrictFunctor U.ι).map t)) := by
  rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff, ← AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff]
  simp only [BinaryTensorId.Construction.BinaryTensorMap.tensorSection, Functor.map_comp, isIso_comp_left_iff]
  exact BinaryTensorIs.Construction.BinaryTensorRestriction.isIso_map_iff U.ι (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) s t

theorem isIso_of_frames (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (h : (Scheme.Modules.pullback U.ι).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    [IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t))] :
    IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) ∧ IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι t) := by
  have := (isIso_on_open_iff s t U).mp inferInstance
  obtain ⟨hs, ht⟩ := BinaryTensorOf.Construction.BinaryTensorInvertibility.of_frames
    ((Scheme.Modules.restrictFunctor U.ι).map s) ((Scheme.Modules.restrictFunctor U.ι).map t)
    (Scheme.Modules.restrictUnitIso U.ι)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e)
    (Scheme.Modules.restrictUnitIso U.ι)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M.sheaf ≪≫ h)
  exact ⟨(AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff U.ι s).mpr ((AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff U.ι s).mp hs),
    (AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff U.ι t).mpr ((AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff U.ι t).mp ht)⟩

theorem nonvanishing_le : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t) ≤
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := by
  intro x hx
  obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
  change X.Opens at U
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t)) := hU
  obtain ⟨V, hxV, ⟨e⟩⟩ := L.locallyTrivial x
  obtain ⟨W, hxW, ⟨h⟩⟩ := M.locallyTrivial x
  let Z : X.Opens := (U ⊓ V) ⊓ W
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection Z.ι (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t)) :=
    AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le (inf_le_left.trans inf_le_left) _
  obtain ⟨hs, ht⟩ := isIso_of_frames s t Z
    (L.frameRestrict (inf_le_left.trans inf_le_right) e) (M.frameRestrict inf_le_right h)
  exact ⟨TopologicalSpace.Opens.mem_sSup.mpr ⟨Z, hs, ⟨⟨hxU, hxV⟩, hxW⟩⟩,
    TopologicalSpace.Opens.mem_sSup.mpr ⟨Z, ht, ⟨⟨hxU, hxV⟩, hxW⟩⟩⟩

theorem le_nonvanishing : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t ≤
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t) := by
  intro x hx
  obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx.1
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.mp hx.2
  change X.Opens at U V
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := hU
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι t) := hV
  have hs : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U ⊓ V).ι s) := AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le inf_le_left s
  have ht : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U ⊓ V).ι t) := AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le inf_le_right t
  have : IsIso ((Scheme.Modules.restrictFunctor (U ⊓ V).ι).map s) :=
    (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff _ s).mpr ((AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff _ s).mp hs)
  have : IsIso ((Scheme.Modules.restrictFunctor (U ⊓ V).ι).map t) :=
    (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff _ t).mpr ((AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff _ t).mp ht)
  have hst := (isIso_on_open_iff s t (U ⊓ V)).mpr inferInstance
  exact TopologicalSpace.Opens.mem_sSup.mpr ⟨U ⊓ V, hst, hxU, hxV⟩

theorem nonvanishing : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t) =
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t :=
  le_antisymm (nonvanishing_le s t) (le_nonvanishing s t)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus
