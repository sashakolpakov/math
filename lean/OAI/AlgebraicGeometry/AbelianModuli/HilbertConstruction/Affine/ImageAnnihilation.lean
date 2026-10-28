import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedPowerAnnihilation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SectionEquality

/-! # Image Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImageAnnihilation

noncomputable section

/-!
The affine annihilation theorem in terms of ordinary section values on image
opens. This is the form needed to remove differences on chart overlaps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L : Y.Modules}

/-- Vanishing on an open persists on any smaller open. -/
theorem module_value_zero_restrict {M : Y.Modules} {A B W : Y.Opens}
    (hAB : A ≤ B) (hWA : W ≤ A) (v : Γ(M, B))
    (hv : M.presheaf.map (homOfLE hAB).op v = 0) :
    M.presheaf.map (homOfLE (hWA.trans hAB)).op v = 0 := by
  have hc := ConcreteCategory.congr_hom
    (M.presheaf.map_comp (homOfLE hAB).op (homOfLE hWA).op) v
  exact hc.trans ((congrArg (fun z : Γ(M, A) => M.presheaf.map (homOfLE hWA).op z) hv).trans
    (map_zero _))

variable (f : X ⟶ Y) [IsOpenImmersion f] [IsAffine X]

/-- On an affine framed chart, a section value vanishing on `D(s)` is killed
by a sufficiently long transition in tensor degree. -/
theorem affine_image_power_annihilation
    (e : Line.Bundles.structureModule X ⟶ L.restrict f) [IsIso e]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ)
    (v : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ ⊤))
    (hv : (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map
      (homOfLE (show (f ''ᵁ ⊤) ⊓ Ample.LineBundles.sectionNonvanishing s ≤ f ''ᵁ ⊤ from inf_le_left)).op v = 0) :
    ∃ m : ℕ, (Power.SectionTransitions.powerSectionTransition s n m).app (f ''ᵁ ⊤) v = 0 := by
  let D := Ample.LineBundles.sectionNonvanishing (Section.SectionRestriction.restrictSection f s)
  let t := (Global.Sections.moduleSectionHomEquiv ((TensorPower.PowerSheaf.tensorPowerModule L n).restrict f)).symm v
  have hD : f ''ᵁ D ≤ (f ''ᵁ ⊤) ⊓ Ample.LineBundles.sectionNonvanishing s := by
    refine le_inf (f.image_mono le_top) ?_
    dsimp [D]
    rw [Section.SectionRestriction.sectionNonvanishing_restrictSection, Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  have hzero := module_value_zero_restrict inf_le_left hD v hv
  have ht : t.app D (1 : Γ(X, D)) = 0 := by
    have hres := Section.Gluing.moduleSectionHomEquiv_restrict
      ((TensorPower.PowerSheaf.tensorPowerModule L n).restrict f) t D
    have htval : Global.Sections.moduleSectionHomEquiv ((TensorPower.PowerSheaf.tensorPowerModule L n).restrict f) t = v :=
      (Global.Sections.moduleSectionHomEquiv ((TensorPower.PowerSheaf.tensorPowerModule L n).restrict f)).apply_symm_apply v
    exact hres.symm.trans ((congrArg (fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ ⊤) =>
      (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (f.opensFunctor.map D.leTop).op z) htval).trans hzero)
  obtain ⟨m, hm⟩ := RestrictedPowerAnnihilation.restricted_power_annihilation f e s n t
    ((Local.SectionEquality.pullbackSection_eq_zero_iff_on_open D t).mpr ht)
  refine ⟨m, ?_⟩
  have hval := congrArg (Global.Sections.moduleSectionHomEquiv ((TensorPower.PowerSheaf.tensorPowerModule L (n + m)).restrict f)) hm
  change (Power.SectionTransitions.powerSectionTransition s n m).app (f ''ᵁ ⊤)
    (Global.Sections.moduleSectionHomEquiv ((TensorPower.PowerSheaf.tensorPowerModule L n).restrict f) t) = 0 at hval
  exact ((congrArg (fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ ⊤) =>
    (Power.SectionTransitions.powerSectionTransition s n m).app (f ''ᵁ ⊤) z)
      ((Global.Sections.moduleSectionHomEquiv ((TensorPower.PowerSheaf.tensorPowerModule L n).restrict f)).apply_symm_apply v)).symm).trans hval

/-- Two section values agreeing on the nonvanishing part of an affine chart
agree everywhere after a sufficiently long degree transition. -/
theorem affine_image_power_equality
    (e : Line.Bundles.structureModule X ⟶ L.restrict f) [IsIso e]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ)
    (v w : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ ⊤))
    (hvw : (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map
      (homOfLE (show (f ''ᵁ ⊤) ⊓ Ample.LineBundles.sectionNonvanishing s ≤ f ''ᵁ ⊤ from inf_le_left)).op v =
      (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map
        (homOfLE (show (f ''ᵁ ⊤) ⊓ Ample.LineBundles.sectionNonvanishing s ≤ f ''ᵁ ⊤ from inf_le_left)).op w) :
    ∃ m : ℕ, (Power.SectionTransitions.powerSectionTransition s n m).app (f ''ᵁ ⊤) v =
      (Power.SectionTransitions.powerSectionTransition s n m).app (f ''ᵁ ⊤) w := by
  obtain ⟨m, hm⟩ := affine_image_power_annihilation f e s n (v - w)
    (by rw [map_sub, hvw, sub_self])
  exact ⟨m, sub_eq_zero.mp ((map_sub _ v w).symm.trans hm)⟩

omit [IsOpenImmersion f] [IsAffine X] in
/-- The equality theorem stated directly on an affine open of the original scheme. -/
theorem affine_open_power_equality (U : Y.Opens) [IsAffine U.toScheme]
    (e : Line.Bundles.structureModule U.toScheme ⟶ L.restrict U.ι) [IsIso e]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) (v w : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, U))
    (hvw : (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map
      (homOfLE (show U ⊓ Ample.LineBundles.sectionNonvanishing s ≤ U from inf_le_left)).op v =
      (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map
        (homOfLE (show U ⊓ Ample.LineBundles.sectionNonvanishing s ≤ U from inf_le_left)).op w) :
    ∃ m : ℕ, (Power.SectionTransitions.powerSectionTransition s n m).app U v =
      (Power.SectionTransitions.powerSectionTransition s n m).app U w := by
  let P (B : Y.Opens) : Prop := ∀ v w : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, B),
    (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map
      (homOfLE (show B ⊓ Ample.LineBundles.sectionNonvanishing s ≤ B from inf_le_left)).op v =
    (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map
      (homOfLE (show B ⊓ Ample.LineBundles.sectionNonvanishing s ≤ B from inf_le_left)).op w →
    ∃ m : ℕ, (Power.SectionTransitions.powerSectionTransition s n m).app B v =
      (Power.SectionTransitions.powerSectionTransition s n m).app B w
  have hP : P (U.ι ''ᵁ ⊤) := fun v w h => affine_image_power_equality U.ι e s n v w h
  exact ((congrArg P U.ι_image_top).mp hP) v w hvw

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImageAnnihilation
