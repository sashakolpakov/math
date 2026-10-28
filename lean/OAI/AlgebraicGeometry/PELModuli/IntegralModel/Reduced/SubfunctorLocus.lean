import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.GeometricLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

/-! # Subfunctor Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.SubfunctorLocus

noncomputable section

/-! An already constructed immersion locus is characterized on every
reduced test scheme by the same condition on all its geometric points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def geometricTestMap {S : Scheme.{0}} {T M : Over S} (x : T ⟶ M)
    {k : Type} [Field k] (p : Spec (.of k) ⟶ T.left) : Over.mk (p ≫ T.hom) ⟶ M :=
  Over.homMk (p ≫ x.left) (by rw [Category.assoc, x.w]; rfl)

theorem immersion_subfunctor_mem_iff_geometric
    {S : Scheme.{0}} {M : Over S} (F : Subfunctor (yoneda.obj M))
    (hF : HilbertScheme.Presentations.SubfunctorRepresentations.ImmersionRepresentable F) (T : Over S) [IsReduced T.left] (x : T ⟶ M) :
    x ∈ F.obj (.op T) ↔
      ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T.left),
        geometricTestMap x p ∈ F.obj (.op (Over.mk (p ≫ T.hom))) := by
  obtain ⟨Z, j, hj, _, e, he⟩ := hF
  let := hj
  rw [HilbertScheme.Presentations.SubfunctorRepresentations.represented_subfunctor_mem F j e he T x]
  constructor
  · rintro ⟨f, hf⟩ k _ _ p
    apply (HilbertScheme.Presentations.SubfunctorRepresentations.represented_subfunctor_mem F j e he _ _).mpr
    let q : Over.mk (p ≫ T.hom) ⟶ Z := Over.homMk (p ≫ f.left) (by rw [Category.assoc, f.w]; rfl)
    refine ⟨q, ?_⟩
    apply Over.OverMorphism.ext
    exact (Category.assoc p f.left j.left).trans (congrArg (p ≫ ·) (congrArg Over.Hom.left hf))
  · intro h
    obtain ⟨g, hg, _⟩ := (GeometricLocus.reduced_immersion_lift_iff_geometric_points j.left x.left).mpr (by
      intro k _ _ p
      obtain ⟨q, hq⟩ := (HilbertScheme.Presentations.SubfunctorRepresentations.represented_subfunctor_mem F j e he _ _).mp (h k p)
      exact ⟨q.left, congrArg Over.Hom.left hq⟩)
    let f : T ⟶ Z := Over.homMk g (by
      rw [← j.w, ← Category.assoc, hg]
      exact x.w)
    exact ⟨f, Over.OverMorphism.ext hg⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.SubfunctorLocus
