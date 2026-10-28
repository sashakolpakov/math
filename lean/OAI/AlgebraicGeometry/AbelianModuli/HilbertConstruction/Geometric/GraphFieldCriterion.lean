import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.EmbeddedGraphNaturality

/-! # Graph Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The embedded graph Hilbert condition is detected by geometric base change to every field-valued parameter point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u

local instance Geometric.GraphFieldCriterion.graphFieldPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))
local instance Geometric.GraphFieldCriterion.graphFieldPullbackFP {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))
local instance Geometric.GraphFieldCriterion.graphFieldPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

theorem Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.of_geometricFieldBaseChanges
    {S : Scheme.{u}} {A B : Over S} {n : ℕ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)
    (T : Over S) (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (s ≫ T.hom) j) P
        (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T) p)) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p := by
  intro K _ s
  let c : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
  let F := (MorphismGraphFamilies.morphismGraphFamily p).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j)
  have hF := F.projectiveBaseChange_affine s (𝟙 (Spec (.of K)))
  rw [Category.id_comp] at hF
  have he := congrArg (fun G : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n) =>
    G.affineProjectivePullback (𝟙 (Spec (.of K)))) (Geometric.EmbeddedGraphNaturality.geometricEmbeddedGraph_baseChange c j p)
  have hfamily := hF.symm.trans he
  exact (congrArg (fun G : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace K n) =>
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial G.homogeneousIdeal.toIdeal P) hfamily).mpr
      (h K s K (𝟙 (Spec (.of K))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
