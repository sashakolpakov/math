import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing
import Mathlib.CategoryTheory.HomCongr

/-! # Sections On Open Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsOnOpenImages

noncomputable section

/-!
Identify sections of canonical pullbacks along open immersions with sections
on their image opens. This permits ordinary sheaf gluing of the local power
sections constructed in the affine-chart extension argument.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The source-frame correction comparing canonical pullback with explicit restriction. -/
def pullbackImageSourceIso : Line.Bundles.structureModule X ≅ Line.Bundles.structureModule X :=
  (Scheme.Modules.restrictUnitIso f).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback f).app (Line.Bundles.structureModule Y) ≪≫
      Line.Bundles.structureModulePullbackIso f

/-- Sections of a pulled-back module on an open immersion are precisely
sections of the original module on the image open. -/
def pullbackSectionImageEquiv (M : Y.Modules) :
    (Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M) ≃ Γ(M, f ''ᵁ ⊤) :=
  ((pullbackImageSourceIso f).symm.homCongr
      ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm).trans
    (Global.Sections.moduleSectionHomEquiv (M.restrict f))

/-- Under the image-section equivalence, a pulled-back global section is its
usual restriction to the image open. -/
theorem pullbackSectionImageEquiv_pullback (M : Y.Modules) (s : Line.Bundles.structureModule Y ⟶ M) :
    pullbackSectionImageEquiv f M (Ample.LineBundles.pullbackSection f s) = s.app (f ''ᵁ ⊤) (1 : Γ(Y, f ''ᵁ ⊤)) := by
  let E := Scheme.Modules.restrictFunctorIsoPullback f
  have h : (pullbackImageSourceIso f).hom ≫ Ample.LineBundles.pullbackSection f s ≫ (E.app M).inv =
      Section.SectionRestriction.restrictSection f s := by
    let u : (Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y) ≅ Line.Bundles.structureModule X :=
      Line.Bundles.structureModulePullbackIso f
    let v : (Line.Bundles.structureModule Y).restrict f ≅ Line.Bundles.structureModule X := Scheme.Modules.restrictUnitIso f
    let E₀ : (Line.Bundles.structureModule Y).restrict f ≅ (Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y) :=
      E.app (Line.Bundles.structureModule Y)
    let E₁ : M.restrict f ≅ (Scheme.Modules.pullback f).obj M := E.app M
    have hn : (Scheme.Modules.restrictFunctor f).map s ≫ E₁.hom =
        E₀.hom ≫ (Scheme.Modules.pullback f).map s := E.hom.naturality s
    change ((v.inv ≫ E₀.hom ≫ u.hom) ≫ (u.inv ≫ (Scheme.Modules.pullback f).map s)) ≫ E₁.inv =
      v.inv ≫ (Scheme.Modules.restrictFunctor f).map s
    calc
      _ = v.inv ≫ (E₀.hom ≫ (Scheme.Modules.pullback f).map s) ≫ E₁.inv := by
        simp only [Category.assoc, u.hom_inv_id_assoc]
      _ = v.inv ≫ ((Scheme.Modules.restrictFunctor f).map s ≫ E₁.hom) ≫ E₁.inv :=
        congrArg (fun z => v.inv ≫ z ≫ E₁.inv) hn.symm
      _ = v.inv ≫ (Scheme.Modules.restrictFunctor f).map s := by
        rw [Category.assoc, E₁.hom_inv_id, Category.comp_id]
  exact (congrArg (Global.Sections.moduleSectionHomEquiv (M.restrict f)) h).trans (Section.SectionRestriction.restrictSection_app_one f s ⊤)

omit [IsOpenImmersion f] in
/-- Compatible image sections glue to a unique global section with the given
canonical pullbacks on all covering schemes. -/
theorem moduleSection_glue_on_open_images (M : Y.Modules) {ι : Type v}
    (T : ι → Scheme.{u}) (g : ∀ i, T i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ g i ''ᵁ (⊤ : (T i).Opens))
    (s : ∀ i, Line.Bundles.structureModule (T i) ⟶ (Scheme.Modules.pullback (g i)).obj M)
    (hs : ∀ i j,
      M.presheaf.map (homOfLE (show (g i ''ᵁ ⊤) ⊓ (g j ''ᵁ ⊤) ≤ g i ''ᵁ ⊤ from inf_le_left)).op
        (pullbackSectionImageEquiv (g i) M (s i)) =
      M.presheaf.map (homOfLE (show (g i ''ᵁ ⊤) ⊓ (g j ''ᵁ ⊤) ≤ g j ''ᵁ ⊤ from inf_le_right)).op
        (pullbackSectionImageEquiv (g j) M (s j))) :
    ∃! t : Line.Bundles.structureModule Y ⟶ M, ∀ i, Ample.LineBundles.pullbackSection (g i) t = s i := by
  obtain ⟨t, ht, huniq⟩ := Section.Gluing.moduleSection_glue M (fun i => g i ''ᵁ ⊤) hg
    (fun i => pullbackSectionImageEquiv (g i) M (s i)) hs
  refine ⟨t, fun i => ?_, fun t' ht' => ?_⟩
  · apply (pullbackSectionImageEquiv (g i) M).injective
    exact (pullbackSectionImageEquiv_pullback (g i) M t).trans (ht i)
  · apply huniq
    intro i
    exact (pullbackSectionImageEquiv_pullback (g i) M t').symm.trans
      (congrArg (pullbackSectionImageEquiv (g i) M) (ht' i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsOnOpenImages
