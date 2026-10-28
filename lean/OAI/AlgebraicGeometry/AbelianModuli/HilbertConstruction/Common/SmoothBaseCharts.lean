import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothBasicOpens

/-! # Smooth Base Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothBaseCharts

noncomputable section

/-! Compatible standard smooth charts for a morphism between schemes smooth over the same base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_common_standardSmooth_charts {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    (d : ℕ) [SmoothOfRelativeDimension d q] [SmoothOfRelativeDimension d (f ≫ q)] (x : X) :
    ∃ (U : S.affineOpens) (V : Y.affineOpens) (W : X.affineOpens), x ∈ W.1 ∧
      ∃ (eq : V.1 ≤ q ⁻¹ᵁ U.1) (ef : W.1 ≤ f ⁻¹ᵁ V.1),
        RingHom.IsStandardSmoothOfRelativeDimension d (q.appLE U.1 V.1 eq).hom ∧
        RingHom.IsStandardSmoothOfRelativeDimension d
          ((f ≫ q).appLE U.1 W.1 (ef.trans (f.preimage_mono eq))).hom := by
  obtain ⟨U, hU, V, hV, hfxV, eq, hq⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := q) (f x)
  obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V from hfxV) (f ⁻¹ᵁ V).isOpen
  obtain ⟨U₀, hU₀, W₀, hW₀, hxW₀, e₀, hp₀⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := d) (f := f ≫ q) x
  obtain ⟨r, s, hxs, ep, hp⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway d).right
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away
    x ⟨U, hU⟩ ⟨U₀, hU₀⟩ ⟨W, hW⟩ ⟨W₀, hW₀⟩ hxW hxW₀ e₀ hp₀ (eq hfxV)
  let V' := Y.basicOpen (q.appLE U V eq r)
  have eq' : V' ≤ q ⁻¹ᵁ S.basicOpen r :=
    (le_of_eq (Scheme.basicOpen_appLE q V U eq r)).trans inf_le_right
  have ef' : X.basicOpen s ≤ f ⁻¹ᵁ V' := by
    intro z hz
    exact (congrArg (fun O : Y.Opens => f z ∈ O) (Scheme.basicOpen_appLE q V U eq r)).mpr
      ⟨hWV (X.basicOpen_le s hz), ep hz⟩
  refine ⟨⟨S.basicOpen r, hU.basicOpen r⟩,
    ⟨V', hV.basicOpen (q.appLE U V eq r)⟩, ⟨X.basicOpen s, hW.basicOpen s⟩,
    hxs, eq', ef', ?_, hp⟩
  exact StandardSmoothBasicOpens.standardSmooth_basicOpen_appLE q hU hV eq d hq r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothBaseCharts
