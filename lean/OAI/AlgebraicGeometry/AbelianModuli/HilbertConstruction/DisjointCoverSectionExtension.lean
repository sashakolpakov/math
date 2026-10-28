import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointOpenSectionGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

/-! # Disjoint Cover Section Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A section on one component of a disjoint open cover extends by zero, and its nonvanishing open is exactly the image of the original nonvanishing open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v}
variable (T : ι → Scheme.{u}) (g : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (g i)]
variable (hg : ∀ x : X, ∃ i, x ∈ g i ''ᵁ (⊤ : (T i).Opens))

include hg

theorem DisjointCoverSectionExtension.moduleSection_extend_by_zero_on_disjoint_cover (M : X.Modules)
    (hdis : Pairwise (fun i j => Disjoint (g i ''ᵁ (⊤ : (T i).Opens)) (g j ''ᵁ (⊤ : (T j).Opens))))
    (i : ι) (s : Line.Bundles.structureModule (T i) ⟶ (Scheme.Modules.pullback (g i)).obj M) :
    ∃ t : Line.Bundles.structureModule X ⟶ M, Ample.LineBundles.pullbackSection (g i) t = s ∧
      ∀ j, j ≠ i → Ample.LineBundles.pullbackSection (g j) t = 0 := by
  classical
  let q : ∀ j, Line.Bundles.structureModule (T j) ⟶ (Scheme.Modules.pullback (g j)).obj M :=
    fun j => if h : j = i then h.symm ▸ s else 0
  obtain ⟨t, ht, _⟩ := DisjointOpenSectionGluing.moduleSection_glue_on_disjoint_open_images M T g hg hdis q
  refine ⟨t, ?_, fun j hj => ?_⟩
  · simpa only [q, dite_eq_left rfl] using ht i
  · simpa only [q, dite_eq_right hj] using ht j

theorem Line.Bundles.LineBundle.sectionNonvanishing_extension_by_zero (L : Line.Bundles.LineBundle X)
    (i : ι) (s : Line.Bundles.structureModule (T i) ⟶ (L.pullback (g i)).sheaf)
    (t : Line.Bundles.structureModule X ⟶ L.sheaf) (hi : Ample.LineBundles.pullbackSection (g i) t = s)
    (hzero : ∀ j, j ≠ i → Ample.LineBundles.pullbackSection (g j) t = 0) :
    Ample.LineBundles.sectionNonvanishing t = g i ''ᵁ Ample.LineBundles.sectionNonvanishing s := by
  apply le_antisymm
  · intro x hx
    obtain ⟨j, y, _, hy⟩ := hg x
    have hyx : g j y ∈ Ample.LineBundles.sectionNonvanishing t := hy.symm ▸ hx
    have hyt : y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (g j) t) :=
      (congrArg (fun U : (T j).Opens => y ∈ U)
        (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange (g j) L t)).mpr hyx
    by_cases hji : j = i
    · subst j
      exact ⟨y, (congrArg (fun z => y ∈ Ample.LineBundles.sectionNonvanishing z) hi).mp hyt, hy⟩
    · have he : Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (g j) t) = ⊥ :=
        (congrArg Ample.LineBundles.sectionNonvanishing (hzero j hji)).trans (L.pullback (g j)).sectionNonvanishing_zero
      have hf : y ∈ (⊥ : (T j).Opens) := (congrArg (fun U : (T j).Opens => y ∈ U) he).mp hyt
      exact hf.elim
  · rintro x ⟨y, hy, hxy⟩
    have hyt : y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (g i) t) :=
      (congrArg (fun z => y ∈ Ample.LineBundles.sectionNonvanishing z) hi).mpr hy
    have hyx : g i y ∈ Ample.LineBundles.sectionNonvanishing t :=
      (congrArg (fun U : (T i).Opens => y ∈ U)
        (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange (g i) L t)).mp hyt
    exact hxy ▸ hyx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
