import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Embedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Generators

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation

noncomputable section

/-!
Construct projective presentations from covering sections with generating
ratios. The generation condition is stated in the actual affine coordinate
rings, with the algebra structure induced by the given structural morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}} {L : X.Modules} {n : ℕ}

/-- The ratios of the section family generate each nonvanishing chart over
the base's global functions. -/
def SectionRatiosGenerate (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) : Prop :=
  ∀ i, letI := ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom.toAlgebra
    Algebra.adjoin Γ(S, ⊤) (Set.range (fun k => Frames.sectionRatio (s i) (s k))) = ⊤

theorem SectionRatiosGenerate.surjective {f : X ⟶ S}
    {s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)} (h : SectionRatiosGenerate f s)
    (i : Fin (n + 1)) : Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
        (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i))) := by
  let := ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom.toAlgebra
  exact ProjectiveChart.Generators.projectiveChartEvaluation_surjective (R := Γ(S, ⊤))
    (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i)) (h i)

/-- A concrete projective presentation over an affine base, from a section
cover with affine nonvanishing opens and generating section ratios. -/
def projectivePresentationOfSections (f : X ⟶ S) [IsAffine S]
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : SectionRatiosGenerate f s) : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) where
  dimension := n
  embedding := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  closedImmersion := Embedding.sectionProjectiveMorphism_closedImmersion f s hs ha hgen.surjective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation
