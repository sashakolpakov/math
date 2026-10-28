import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsClosed
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.DegreeIsoBaseChange

/-! # Generation Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationIso.BundleCycles

noncomputable section

section

/-! Generation by actual projective Chow components transfers
through genuine relative scheme and line-bundle isomorphisms. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem projectiveChowGeneration_of_iso {E D X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian D] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [D.IsSeparated] (p : E ⟶ X) (q : D ⟶ X)
    [Smooth p] [Smooth q] [GeometricallyIntegral p] [GeometricallyIntegral q]
    (j : D ⟶ E) [IsIso j] (hj : j ≫ p = q) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : (L.pullback j).sheaf ≅ M.sheaf)
    (hgen : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ (q ≫ f) d), α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated q f r hq M d)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) : α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated p f r hp L d := by
  have h : j ≫ (p ≫ f) = q ≫ f := by rw [← Category.assoc, hj]
  obtain ⟨β, hβ⟩ := (Closed.ChowOver.BundleCycles.schemeIsoChowEquiv (asIso j) (q ≫ f) (p ≫ f) h d).surjective α
  change Closed.ChowOver.BundleCycles.closedChowPushforwardOver j (q ≫ f) (p ≫ f) h d β = α at hβ
  have hs : IsPullback q j (𝟙 X) p := IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hj]⟩
  have HC := ProjectiveChow.GeneratorsClosed.BundleCycles.projectiveChowGenerated_closedPushforward p q (𝟙 X) j hs f r hp hq L d
  have hβgen : β ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated q f r hq (L.pullback j) d := by
    rw [ProjectiveChow.GeneratorsIso.BundleCycles.projectiveChowGenerated_lineBundleIso q f r hq e]
    exact hgen d β
  have H := HC β hβgen
  change Closed.ChowOver.BundleCycles.closedChowPushforwardOver j (q ≫ f) (p ≫ f) h d β ∈ _ at H
  rwa [hβ] at H

theorem projectiveChowGeneration_iso_baseChange {E D X Y : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : E ⟶ X) (q : D ⟶ X) [IsProper p] [IsProper q] [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (j : D ⟶ E) [IsIso j] (hj : j ≫ p = q) (b : Y ⟶ X)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : (L.pullback j).sheaf ≅ M.sheaf)
    (hgen : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd q b ≫ f) d),
      α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd q b) f r (hq.baseChange b) (M.pullback (pullback.fst q b)) d)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd p b ≫ f) d) :
    α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd p b) f r (hp.baseChange b) (L.pullback (pullback.fst p b)) d := by
  let k := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p q j hj b
  let e' := LineBundle.PullbackIso.Cycles.lineBundlePullbackSquareIso L M (pullback.fst p b) j k (pullback.fst q b)
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_fst p q j hj b) e
  exact projectiveChowGeneration_of_iso (pullback.snd p b) (pullback.snd q b) k
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd p q j hj b) f r (hp.baseChange b) (hq.baseChange b)
    (L.pullback (pullback.fst p b)) (M.pullback (pullback.fst q b)) e' hgen d α

end

/-! The actual associativity isomorphism of scheme pullbacks
transports projective Chow generation across iterated base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X Y Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Z] [Z.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (b : Y ⟶ X) (c : Z ⟶ Y) (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (hgen : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd p (c ≫ b) ≫ f) d),
      α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd p (c ≫ b)) f r (hp.baseChange (c ≫ b))
        (L.pullback (pullback.fst p (c ≫ b))) d)

include hgen in
theorem projectiveChowGeneration_iteratedBaseChange (d : ℕ)
    (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd (pullback.snd p b) c ≫ f) d) :
    α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd (pullback.snd p b) c) f r ((hp.baseChange b).baseChange c)
      ((L.pullback (pullback.fst p b)).pullback (pullback.fst (pullback.snd p b) c)) d := by
  let u := pullback.fst (pullback.snd p b) c
  let v := pullback.fst p b
  have H : IsPullback (pullback.snd (pullback.snd p b) c) (u ≫ v) (c ≫ b) p :=
    (IsPullback.of_hasPullback (pullback.snd p b) c).flip.paste_vert (IsPullback.of_hasPullback p b).flip
  let e := H.flip.isoPullback
  let hL := LineBundle.PullbackIso.Cycles.lineBundlePullbackIso (LineBundle.PullbackIso.Cycles.lineBundlePullbackCompIso L u v) e.inv ≪≫
    LineBundle.PullbackIso.Cycles.lineBundlePullbackCompIso L e.inv (u ≫ v) ≪≫ LineBundle.PullbackIso.Cycles.lineBundlePullbackCongrIso L H.flip.isoPullback_inv_fst
  exact projectiveChowGeneration_of_iso (pullback.snd (pullback.snd p b) c) (pullback.snd p (c ≫ b))
    e.inv H.flip.isoPullback_inv_snd f r ((hp.baseChange b).baseChange c) (hp.baseChange (c ≫ b))
    ((L.pullback v).pullback u) (L.pullback (pullback.fst p (c ≫ b))) hL hgen d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationIso.BundleCycles
