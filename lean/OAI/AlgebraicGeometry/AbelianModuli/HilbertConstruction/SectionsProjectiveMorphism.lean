import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ChartOverlaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveCharts
import Mathlib.AlgebraicGeometry.Gluing

/-! # Sections Projective Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism

noncomputable section

/-! A family of sections whose nonvanishing opens cover defines an actual global morphism
to relative projective space. This constructs a morphism, not an immersion or an HilbertConstruction moduli scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}} {L : X.Modules} {n : ℕ}

/-- The actual open cover supplied by the nonvanishing opens of a section family. -/
def sectionOpenCover (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) : Scheme.OpenCover.{0} X where
  I₀ := Fin (n + 1)
  X i := (Ample.LineBundles.sectionNonvanishing (s i)).toScheme
  f i := (Ample.LineBundles.sectionNonvanishing (s i)).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := hs x
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩

/-- Glue the section-chart maps into a morphism to projective space over the global base ring. -/
def sectionAbsoluteMorphism (f : X ⟶ S) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    X ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
  (sectionOpenCover s hs).glueMorphisms (Section.ChartOverlaps.sectionAbsoluteChart f s) (Section.ChartOverlaps.sectionAbsoluteChart_overlap f s)

/-- On every nonvanishing open, the global morphism is its explicit section-ratio chart map. -/
theorem sectionAbsoluteMorphism_restrict (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) (i : Fin (n + 1)) :
    (Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ sectionAbsoluteMorphism f s hs = Section.ChartOverlaps.sectionAbsoluteChart f s i :=
  (sectionOpenCover s hs).ι_glueMorphisms (Section.ChartOverlaps.sectionAbsoluteChart f s) (Section.ChartOverlaps.sectionAbsoluteChart_overlap f s) i

theorem sectionAbsoluteChart_over (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i : Fin (n + 1)) :
    Section.ChartOverlaps.sectionAbsoluteChart f s i ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom =
      ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f) ≫ S.toSpecΓ :=
  (ProjectiveChart.Evaluation.projectiveChartMap_over ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
    (fun k => Section.Frames.sectionRatio (s i) (s k)) i (Section.Frames.sectionRatio_self (s i))).trans
      (Scheme.toSpecΓ_naturality ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f)).symm

/-- The glued morphism has the prescribed structural map to the base ring. -/
theorem sectionAbsoluteMorphism_over (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    sectionAbsoluteMorphism f s hs ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom = f ≫ S.toSpecΓ := by
  apply (sectionOpenCover s hs).hom_ext
  intro i
  exact (Category.assoc (Ample.LineBundles.sectionNonvanishing (s i)).ι _ _).symm.trans
    ((congrArg (fun a => a ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom)
      (sectionAbsoluteMorphism_restrict f s hs i)).trans
        ((sectionAbsoluteChart_over f s i).trans (Category.assoc _ _ _)))

/-- Sections with a covering family of nonvanishing opens define a morphism to relative projective space. -/
def sectionProjectiveMorphism (f : X ⟶ S) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) : Over.mk f ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  Over.homMk (pullback.lift (sectionAbsoluteMorphism f s hs) f (sectionAbsoluteMorphism_over f s hs))
    (pullback.lift_snd _ _ _)

/-- The constructed relative morphism lies over the original scheme morphism. -/
theorem sectionProjectiveMorphism_over (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    (sectionProjectiveMorphism f s hs).left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom = f :=
  (sectionProjectiveMorphism f s hs).w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism
