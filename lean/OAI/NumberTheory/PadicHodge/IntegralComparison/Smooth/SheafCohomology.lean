import OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech

/-! # Sheaf Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.SheafCohomology

noncomputable section

/-! Higher cohomology vanishes on actual open restrictions of smooth
form sheaves, also after forgetting complex scalars. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

local instance (X : TopCat.{0}) : HasExt.{1} (AlgebraicGeometry.Comparison.Betti.ConstantSheafSections.ComplexSheaves X) :=
  HasExt.standard _

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem restricted_acyclic (O : Opens M) [SigmaCompactSpace O] (p q : ℕ) :
    Subsingleton (Sheaf.H.{0}
      ((AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat O.isOpenEmbedding).obj
        ((AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque.sheafForget (TopCat.of M)).obj (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p)))
      (q + 1)) := by
  let F := AlgebraicGeometry.Comparison.Betti.RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p
  have := AlgebraicGeometry.Comparison.Betti.RestrictedSmoothAcyclicity.Godement.restrictedSmoothFormSheaf_ext_vanish (E := E) O p q
  exact (AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology.complexSheafCohomologyForgetEquiv (TopCat.of O) F
    (q + 1)).symm.injective.subsingleton

theorem cech_acyclic [SecondCountableTopology M] [LocallyCompactSpace M]
    {ι : Type} (U : ι → Opens M) (r : ℕ) :
    AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of M) U
      ((AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque.sheafForget (TopCat.of M)).obj (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M r)) := by
  intro p t q
  let O : Opens M := ∏ᶜ fun k : Fin (p + 1) => U (t k)
  have : LocallyCompactSpace O := O.isOpenEmbedding'.locallyCompactSpace
  exact restricted_acyclic (E := E) O r q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.SheafCohomology
