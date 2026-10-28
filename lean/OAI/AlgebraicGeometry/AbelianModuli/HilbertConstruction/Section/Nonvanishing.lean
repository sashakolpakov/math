import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing

noncomputable section

/-! Nonvanishing of sections and its behavior under restriction to open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

private theorem isIso_map_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (s : M ⟶ N) [IsIso (F.map s)] :
    IsIso (G.map s) := by
  have h : e.inv.app M ≫ F.map s ≫ e.hom.app N = G.map s := by
    rw [e.hom.naturality]
    simp
  rw [← h]
  infer_instance

private theorem isIso_map_iff_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (s : M ⟶ N) :
    IsIso (F.map s) ↔ IsIso (G.map s) := by
  constructor
  · intro h
    let := h
    exact isIso_map_of_natIso e s
  · intro h
    let := h
    exact isIso_map_of_natIso e.symm s

/-- Pullback along a scheme isomorphism reflects invertible module-sheaf maps. -/
theorem isIso_pullback_map_iff (f : X ⟶ Y) [IsIso f] {M N : Y.Modules} (s : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback f).map s) ↔ IsIso s := by
  constructor
  · intro h
    let := h
    have : IsIso ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (inv f)).map s) :=
      inferInstanceAs (IsIso ((Scheme.Modules.pullback (inv f)).map
        ((Scheme.Modules.pullback f).map s)))
    exact isIso_map_of_natIso
      (Scheme.Modules.pullbackComp (inv f) f ≪≫
        Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId Y) s
  · intro h
    let := h
    infer_instance

/-- The choice of the structure-module comparison does not affect invertibility of a section. -/
theorem isIso_pullbackSection_iff (f : X ⟶ Y) {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) :
    IsIso (Ample.LineBundles.pullbackSection f s) ↔ IsIso ((Scheme.Modules.pullback f).map s) :=
  isIso_comp_left_iff (Line.Bundles.structureModulePullbackIso f).inv ((Scheme.Modules.pullback f).map s)

/-- A local frame remains a local frame under any pullback. -/
instance pullbackSection_isIso (f : X ⟶ Y) {M : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ M) [IsIso s] : IsIso (Ample.LineBundles.pullbackSection f s) :=
  (isIso_pullbackSection_iff f s).mpr inferInstance

/-- Successive section pullbacks and composite pullback have the same invertibility condition. -/
theorem isIso_pullbackSection_comp_iff (f : Y ⟶ Z) (h : X ⟶ Y) {M : Z.Modules}
    (s : Line.Bundles.structureModule Z ⟶ M) :
    IsIso (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s)) ↔ IsIso (Ample.LineBundles.pullbackSection (h ≫ f) s) := by
  simp only [Ample.LineBundles.pullbackSection, Functor.map_comp, isIso_comp_left_iff]
  exact isIso_map_iff_of_natIso (Scheme.Modules.pullbackComp h f) s

/-- Precomposition by an isomorphism does not change the local-frame condition. -/
theorem isIso_pullbackSection_comp_iso_iff (f : Y ⟶ Z) (h : X ⟶ Y) [IsIso h]
    {M : Z.Modules} (s : Line.Bundles.structureModule Z ⟶ M) :
    IsIso (Ample.LineBundles.pullbackSection (h ≫ f) s) ↔ IsIso (Ample.LineBundles.pullbackSection f s) :=
  (isIso_pullbackSection_comp_iff f h s).symm.trans
    ((isIso_pullbackSection_iff h (Ample.LineBundles.pullbackSection f s)).trans
      (isIso_pullback_map_iff h (Ample.LineBundles.pullbackSection f s)))

/-- Frames on an open part of an open subscheme are exactly frames on its image open. -/
theorem isIso_pullbackSection_image_iff (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) (U : X.Opens) :
    IsIso (Ample.LineBundles.pullbackSection U.ι (Ample.LineBundles.pullbackSection f s)) ↔
      IsIso (Ample.LineBundles.pullbackSection (f ''ᵁ U).ι s) :=
  (isIso_pullbackSection_comp_iff f U.ι s).trans
    ((congrArg (fun a : U.toScheme ⟶ Y => IsIso (Ample.LineBundles.pullbackSection a s))
      (f.isoImage_hom_ι U).symm).to_iff.trans
        (isIso_pullbackSection_comp_iso_iff (f ''ᵁ U).ι (f.isoImage U).hom s))

/-- A frame on an open of the target pulls back to a frame on its preimage. -/
theorem isIso_pullbackSection_preimage (f : X ⟶ Y) {M : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ M) (V : Y.Opens) [IsIso (Ample.LineBundles.pullbackSection V.ι s)] :
    IsIso (Ample.LineBundles.pullbackSection (f ⁻¹ᵁ V).ι (Ample.LineBundles.pullbackSection f s)) := by
  apply (isIso_pullbackSection_comp_iff f (f ⁻¹ᵁ V).ι s).mpr
  have h : IsIso (Ample.LineBundles.pullbackSection ((f ∣_ V) ≫ V.ι) s) :=
    (isIso_pullbackSection_comp_iff V.ι (f ∣_ V) s).mp inferInstance
  exact (congrArg (fun a : (f ⁻¹ᵁ V).toScheme ⟶ Y => IsIso (Ample.LineBundles.pullbackSection a s))
    (morphismRestrict_ι f V)).mp h

/-- Restricting a section pulls back its nonvanishing open. -/
theorem sectionNonvanishing_pullback (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) = f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s := by
  ext x
  change x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) ↔ f x ∈ Ample.LineBundles.sectionNonvanishing s
  simp only [Ample.LineBundles.sectionNonvanishing, TopologicalSpace.Opens.mem_sSup, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨U, hU, hx⟩
    exact ⟨f ''ᵁ U, (isIso_pullbackSection_image_iff f s U).mp hU, ⟨x, hx, rfl⟩⟩
  · rintro ⟨V, hV, hx⟩
    let := hV
    exact ⟨f ⁻¹ᵁ V, isIso_pullbackSection_preimage f s V, hx⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing
