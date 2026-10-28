import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionMultiplication

/-! # Integral Line Bundle Monomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A line-bundle map that is an isomorphism on a nonempty open of an integral scheme is a monomorphism of the actual module sheaves. In particular, multiplication by a generically nonvanishing line-bundle section has an actual short exact cokernel sequence. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} [IsIntegral X] (L M : Line.Bundles.LineBundle X)

theorem Line.Bundles.LineBundle.mapSections_injective_of_nonempty_open
    (φ : L.sheaf ⟶ M.sheaf) (U : X.Opens) [Nonempty U]
    [IsIso ((Scheme.Modules.pullback U.ι).map φ)] (V : X.Opens) :
    Function.Injective (φ.app V) := by
  intro s t hst
  by_cases hV : Nonempty V
  · let W : X.Opens := V ⊓ U
    have : Nonempty W := by
      have hnon := nonempty_preirreducible_inter V.isOpen U.isOpen
        (show (V : Set X).Nonempty from ⟨(Classical.choice hV).val, (Classical.choice hV).property⟩)
        (show (U : Set X).Nonempty from
          ⟨(Classical.choice (inferInstance : Nonempty U)).val,
            (Classical.choice (inferInstance : Nonempty U)).property⟩)
      exact hnon.to_subtype
    have hWV : W ≤ V := inf_le_left
    have hWU : W ≤ U.ι.opensRange := by
      rw [U.opensRange_ι]
      exact inf_le_right
    apply L.restriction_injective hWV
    apply (OpenPullback.FrameEquivalence.openPullbackModuleEquiv U.ι (asIso ((Scheme.Modules.pullback U.ι).map φ)) W hWU).injective
    rw [Section.LocalLinearFrames.openPullbackModuleEquiv_global_apply, Section.LocalLinearFrames.openPullbackModuleEquiv_global_apply]
    exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hWV).op) s).trans
      ((congrArg (M.sheaf.presheaf.map (homOfLE hWV).op) hst).trans
        (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hWV).op) t).symm)
  · apply L.sheaf.isSheaf.section_ext
    intro x hx
    exact False.elim (hV ⟨⟨x, hx⟩⟩)

theorem Line.Bundles.LineBundle.mono_of_nonempty_open_isIso
    (φ : L.sheaf ⟶ M.sheaf) (U : X.Opens) [Nonempty U]
    [IsIso ((Scheme.Modules.pullback U.ι).map φ)] : Mono φ := by
  refine ⟨fun {Z} f g h => ?_⟩
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro x
  apply L.mapSections_injective_of_nonempty_open M φ U V
  exact ConcreteCategory.congr_hom (congrArg (fun q : Z ⟶ M.sheaf => q.app V) h) x

theorem IntegralLineBundleMonomorphisms.lineBundleSectionMultiply_mono
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [Nonempty (Ample.LineBundles.sectionNonvanishing s)] :
    Mono (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s) := by
  have : IsIso ((Scheme.Modules.pullback (Ample.LineBundles.sectionNonvanishing s).ι).map
      (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s)) :=
    LineBundle.SectionMultiplication.lineBundleSectionMultiply_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι L M s
  exact M.mono_of_nonempty_open_isIso (L.tensor M)
    (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s) (Ample.LineBundles.sectionNonvanishing s)

theorem IntegralLineBundleMonomorphisms.lineBundle_section_mono
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [Nonempty (Ample.LineBundles.sectionNonvanishing s)] : Mono s := by
  have hIso : IsIso ((Scheme.Modules.pullback (Ample.LineBundles.sectionNonvanishing s).ι).map s) :=
    (Section.Nonvanishing.isIso_pullbackSection_iff (Ample.LineBundles.sectionNonvanishing s).ι s).mp
      (Section.Frames.pullbackSection_nonvanishing_isIso s)
  exact @Line.Bundles.LineBundle.mono_of_nonempty_open_isIso X inferInstance (Line.Bundles.LineBundle.trivial X) L s
    (Ample.LineBundles.sectionNonvanishing s) inferInstance hIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
