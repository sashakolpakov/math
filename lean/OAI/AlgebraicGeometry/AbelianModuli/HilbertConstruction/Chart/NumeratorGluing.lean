import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OverlapStabilization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Extensions

/-! # Numerator Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
On a quasi-compact separated scheme, local power numerators become compatible
after a common degree transition and glue to a global section.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {Y : Scheme.{u}} [Y.IsSeparated]

/-- Numerators on a finite affine frame cover glue after one common transition. -/
theorem Line.Bundles.LineBundle.glue_chart_numerators (L : Line.Bundles.LineBundle Y) {ι : Type v} [Fintype ι]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
      Line.Bundles.structureModule (U i).toScheme))
    (cover : ∀ y : Y, ∃ i, y ∈ U i)
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : ∀ i, Line.Bundles.structureModule (U i).toScheme ⟶
      (Scheme.Modules.pullback (U i).ι).obj (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n))
    (ht : ∀ i, Common.DegreeChartExtensions.ChartPowerExtends (U i).ι s r n (t i)) :
    ∃ (m : ℕ) (a : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf (n + m)),
      ∀ i, Ample.LineBundles.pullbackSection (U i).ι a =
        t i ≫ (Scheme.Modules.pullback (U i).ι).map (Power.SectionTransitions.powerSectionTransition s n m) := by
  classical
  let V (i : ι) := (U i).ι ''ᵁ ⊤
  let W (p : ι × ι) := V p.1 ⊓ V p.2
  let v (p : ι × ι) : Γ(TensorPower.PowerSheaf.tensorPowerModule L.sheaf n, W p) :=
    (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n).presheaf.map (homOfLE inf_le_left).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv (U p.1).ι (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) (t p.1))
  let w (p : ι × ι) : Γ(TensorPower.PowerSheaf.tensorPowerModule L.sheaf n, W p) :=
    (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n).presheaf.map (homOfLE inf_le_right).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv (U p.2).ι (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) (t p.2))
  have hV (i : ι) : IsAffineOpen (V i) :=
    (congrArg IsAffineOpen (U i).ι_image_top).mpr (hU i)
  have heventual (p : ι × ι) : ∃ m : ℕ,
      (Power.SectionTransitions.powerSectionTransition s n m).app (W p) (v p) =
        (Power.SectionTransitions.powerSectionTransition s n m).app (W p) (w p) := by
    have : IsAffine (W p).toScheme := (hV p.1).inf (hV p.2)
    let e : Line.Bundles.structureModule (W p).toScheme ⟶ L.sheaf.restrict (W p).ι :=
      (L.frameRestrict (inf_le_left.trans (U p.1).ι_image_top.le) (frames p.1).some).inv ≫
        ((Scheme.Modules.restrictFunctorIsoPullback (W p).ι).app L.sheaf).inv
    have : IsIso e := inferInstanceAs (IsIso (_ ≫ _))
    exact Common.DegreeChartExtensions.ChartPowerExtends.eventual_overlap_values (U p.1).ι (U p.2).ι s r n
      (t p.1) (t p.2) (ht p.1) (ht p.2) (W p) e inf_le_left inf_le_right
  obtain ⟨m, hm⟩ := OverlapStabilization.powerTransition_value_eq_uniform s n W v w heventual
  let t' (i : ι) := t i ≫ (Scheme.Modules.pullback (U i).ι).map (Power.SectionTransitions.powerSectionTransition s n m)
  have hcover : ∀ y : Y, ∃ i, y ∈ (U i).ι ''ᵁ (⊤ : (U i).toScheme.Opens) := by
    intro y
    obtain ⟨i, hi⟩ := cover y
    exact ⟨i, (congrArg (fun B : Y.Opens => y ∈ B) (U i).ι_image_top).mpr hi⟩
  have hcompat (i j : ι) :
      (TensorPower.PowerSheaf.tensorPowerModule L.sheaf (n + m)).presheaf.map
        (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op
          (SectionsOnOpenImages.pullbackSectionImageEquiv (U i).ι (TensorPower.PowerSheaf.tensorPowerModule L.sheaf (n + m)) (t' i)) =
      (TensorPower.PowerSheaf.tensorPowerModule L.sheaf (n + m)).presheaf.map
        (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op
          (SectionsOnOpenImages.pullbackSectionImageEquiv (U j).ι (TensorPower.PowerSheaf.tensorPowerModule L.sheaf (n + m)) (t' j)) :=
    (OverlapStabilization.image_section_postcomp_restrict (U i).ι (t i) (Power.SectionTransitions.powerSectionTransition s n m)
      (W (i, j)) inf_le_left).trans ((hm (i, j)).trans
        (OverlapStabilization.image_section_postcomp_restrict (U j).ι (t j) (Power.SectionTransitions.powerSectionTransition s n m)
          (W (i, j)) inf_le_right).symm)
  obtain ⟨a, ha, _⟩ := SectionsOnOpenImages.moduleSection_glue_on_open_images (TensorPower.PowerSheaf.tensorPowerModule L.sheaf (n + m))
    (fun i => (U i).toScheme) (fun i => (U i).ι) hcover t' hcompat
  exact ⟨m, a, ha⟩

/-- A function on `D(s)` admits a global positive-degree numerator whose
restrictions have the prescribed ratio on a finite affine cover. -/
theorem Line.Bundles.LineBundle.exists_global_chart_extension (L : Line.Bundles.LineBundle Y) [CompactSpace Y]
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n) (a : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)
      (k : ℕ) (U : Fin k → Y.Opens),
      (∀ y : Y, ∃ i, y ∈ U i) ∧
      ∀ i, Common.DegreeChartExtensions.ChartPowerExtends (U i).ι s r n (Ample.LineBundles.pullbackSection (U i).ι a) := by
  obtain ⟨k, U, hU, frames, cover, n, hn, t, ht⟩ := L.exists_common_degree_open_extensions s r
  obtain ⟨m, a, ha⟩ := L.glue_chart_numerators U hU frames cover s r n t ht
  refine ⟨n + m, Nat.add_pos_left hn m, a, k, U, cover, fun i => ?_⟩
  exact (congrArg (Common.DegreeChartExtensions.ChartPowerExtends (U i).ι s r (n + m)) (ha i)).mpr
    (Common.DegreeChartExtensions.ChartPowerExtends.transition (U i).ι s r n m (t i) (ht i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
