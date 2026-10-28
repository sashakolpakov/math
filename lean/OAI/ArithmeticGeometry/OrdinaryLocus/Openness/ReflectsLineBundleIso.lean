import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRestriction
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UnitEndIso
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction

/-! # Reflects Line Bundle Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ReflectsLineBundleIso.Construction

noncomputable section

/-! A section detects invertibility of a line-bundle map with relative local frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_unitEnd_of_pullback_appTop_iso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f.appTop]
    (q : End (LineBundle.Construction.structureSheafModule X)) [IsIso ((Scheme.Modules.pullback f).map q)] : IsIso q := by
  let e := (asIso f.appTop).commRingCatIsoToRingEquiv
  have hu := (UnitEndPullback.Construction.isIso_pullback_unitEnd_iff f q).mp inferInstance
  change IsUnit (e (ModuleSections.Construction.structureSheafEndRingEquiv X q)) at hu
  apply (UnitEndPullback.Construction.structureSheafEnd_isIso_iff X q).mpr
  simpa only [RingEquiv.symm_apply_apply] using hu.map e.symm

theorem isIso_trivialBundle_map_of_pullback_appTop_iso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f.appTop]
    (L : X.Modules) (e : L ≅ LineBundle.Construction.structureSheafModule X) (q : LineBundle.Construction.structureSheafModule X ⟶ L)
    [IsIso ((Scheme.Modules.pullback f).map q)] : IsIso q := by
  have : IsIso ((Scheme.Modules.pullback f).map (q ≫ e.hom)) := by
    rw [(Scheme.Modules.pullback f).map_comp]
    infer_instance
  have : IsIso (q ≫ e.hom) := isIso_unitEnd_of_pullback_appTop_iso f (q ≫ e.hom)
  exact IsIso.of_isIso_comp_right q e.hom

theorem section_reflects_isIso_of_relative_frames
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (hf : ∀ U : S.Opens, IsIso (π.app U)) (L : X.Modules)
    (hloc : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj L ≅ LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ U).toScheme))
    (q : LineBundle.Construction.structureSheafModule X ⟶ L) [IsIso ((Scheme.Modules.pullback s).map q)] : IsIso q := by
  apply ModuleLocalIso.Construction.isIso_of_locally_isIso_pullback q
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hloc (π x)
  let V := π ⁻¹ᵁ U
  let sU := SectionRestriction.Construction.sectionRestrict π s hs U
  let L' := (Scheme.Modules.pullback V.ι).obj L
  let qU : LineBundle.Construction.structureSheafModule V.toScheme ⟶ L' :=
    (LineBundle.Construction.pullbackStructureSheafIso V.ι).inv ≫ (Scheme.Modules.pullback V.ι).map q
  have : IsIso sU.appTop := SectionRestriction.Construction.isIso_sectionRestrict_appTop π s hs hf U
  have : IsIso ((Scheme.Modules.pullback (U.ι ≫ s)).map q) := ModuleIso.Construction.isIso_pullbackMap_comp s U.ι q
  have : IsIso ((Scheme.Modules.pullback (sU ≫ V.ι)).map q) :=
    ModuleIso.Construction.isIso_map_of_naturalIso (Scheme.Modules.pullbackCongr (SectionRestriction.Construction.sectionRestrict_ι π s hs U).symm) q
  have hd : IsIso ((Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback sU).map q) :=
    ModuleIso.Construction.isIso_map_of_naturalIso (Scheme.Modules.pullbackComp sU V.ι).symm q
  have : IsIso ((Scheme.Modules.pullback sU).map ((Scheme.Modules.pullback V.ι).map q)) := hd
  have : IsIso ((Scheme.Modules.pullback sU).map qU) := by
    change IsIso ((Scheme.Modules.pullback sU).map (_ ≫ _))
    rw [(Scheme.Modules.pullback sU).map_comp]
    infer_instance
  have hqU : IsIso qU := isIso_trivialBundle_map_of_pullback_appTop_iso sU L' e qU
  have : IsIso ((Scheme.Modules.pullback V.ι).map q) :=
    IsIso.of_isIso_comp_left (LineBundle.Construction.pullbackStructureSheafIso V.ι).inv ((Scheme.Modules.pullback V.ι).map q)
  exact ⟨V, hx, this⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ReflectsLineBundleIso.Construction
