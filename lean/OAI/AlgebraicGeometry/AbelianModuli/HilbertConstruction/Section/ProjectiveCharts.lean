import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

/-! # Projective Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveCharts

noncomputable section

/-! Local morphisms to relative projective space defined by actual line-bundle section ratios. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T X : Scheme.{u}} {n : ℕ}

/-- Normalized regular coordinates over an arbitrary base define a relative projective-chart map. -/
def projectiveChartMapOver (f : T ⟶ S) (v : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (hi : v i = 1) : Over.mk f ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n := by
  let p := ProjectiveChart.Evaluation.projectiveChartMap f.appTop.hom v i hi
  have hp : p ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom = f ≫ S.toSpecΓ :=
    (ProjectiveChart.Evaluation.projectiveChartMap_over f.appTop.hom v i hi).trans (Scheme.toSpecΓ_naturality f).symm
  exact Over.homMk (pullback.lift p f hp) (pullback.lift_snd p f hp)

/-- On the open where one section is nonvanishing, its ratios give a projective-chart map. -/
def sectionProjectiveChart {L : X.Modules} (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i : Fin (n + 1)) :
    Over.mk ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  projectiveChartMapOver ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f)
    (fun j => Frames.sectionRatio (s i) (s j)) i (Frames.sectionRatio_self (s i))

/-- The constructed chart map commutes with the original morphism to the base. -/
theorem sectionProjectiveChart_over {L : X.Modules} (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i : Fin (n + 1)) :
    (sectionProjectiveChart f s i).left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom =
      (Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f :=
  (sectionProjectiveChart f s i).w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveCharts
