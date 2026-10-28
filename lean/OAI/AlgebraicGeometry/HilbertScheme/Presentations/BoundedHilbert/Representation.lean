import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Data
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization

/-! # Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Representation.GradedHilbert

noncomputable section

/-! The glued bounded Hilbert parameter scheme represents the local chart
conditions on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n N : ℕ) (S : Scheme.{u}) (q : ℕ → ℕ)

def boundedHilbertLocalCondition {T : Over S}
    (x : T ⟶ Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S) : Prop :=
  ∃ V : T.left.OpenCover.{u}, ∀ i, ∃ a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N,
    ∃ g : V.X i ⟶ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).left,
      g ≫ (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q).left = V.f i ≫ x.left

theorem boundedHilbertLocalCondition_iff_lift {T : Over S}
    (x : T ⟶ Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S) :
    boundedHilbertLocalCondition n N S q x ↔
      ∃! y : T ⟶ Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q,
        y ≫ Data.GradedHilbert.boundedHilbertParameterOver n N S q = x := by
  constructor
  · rintro ⟨V, hV⟩
    let s : Data.GradedHilbert.boundedHilbertScheme (ι := ι) n N S q ⟶
        (Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S).left := Data.GradedHilbert.boundedHilbertParameter n N S q
    have : Mono s := Data.GradedHilbert.boundedHilbertParameter_mono n N S q
    obtain ⟨g, hg, _⟩ := Local.MorphismFactorization.lift_of_openCover V x.left s (by
      intro i
      obtain ⟨a, k, hk⟩ := hV i
      refine ⟨k ≫ Data.GradedHilbert.boundedHilbertChartMap n N S q a, ?_⟩
      have hc : Data.GradedHilbert.boundedHilbertChartMap n N S q a ≫ s = (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q).left :=
        Data.GradedHilbert.boundedHilbertChartMap_parameter n N S q a
      exact (Category.assoc _ _ _).trans ((congrArg (fun l => k ≫ l) hc).trans hk))
    let y : T ⟶ Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q := Over.homMk g (by
      change g ≫ (s ≫ (Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S).hom) = T.hom
      rw [← Category.assoc, hg, x.w])
    have hy : y ≫ Data.GradedHilbert.boundedHilbertParameterOver n N S q = x := Over.OverMorphism.ext hg
    exact ⟨y, hy, fun z hz => (cancel_mono (Data.GradedHilbert.boundedHilbertParameterOver n N S q)).mp (hz.trans hy.symm)⟩
  · rintro ⟨y, hy, _⟩
    let G := Data.GradedHilbert.boundedHilbertGlueData (ι := ι) n N S q
    let yl : T.left ⟶ G.glued := y.left
    let s : G.glued ⟶ (Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S).left :=
      Data.GradedHilbert.boundedHilbertParameter n N S q
    let V := G.openCover.pullback₁ yl
    refine ⟨V, ?_⟩
    intro a
    change ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N at a
    refine ⟨a, G.openCover.pullbackHom yl a, ?_⟩
    have hc : G.openCover.f a ≫ s = (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q).left :=
      Data.GradedHilbert.boundedHilbertChartMap_parameter n N S q a
    have hys : yl ≫ s = x.left := congrArg Over.Hom.left hy
    calc
      G.openCover.pullbackHom yl a ≫ (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q).left =
          G.openCover.pullbackHom yl a ≫ (G.openCover.f a ≫ s) := congrArg _ hc.symm
      _ = (V.f a ≫ yl) ≫ s := (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ s) (G.openCover.pullbackHom_map yl a))
      _ = V.f a ≫ x.left := (Category.assoc _ _ _).trans (congrArg _ hys)

def boundedHilbertSubfunctor :
    Subfunctor (yoneda.obj (Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S)) where
  obj _T := {x | boundedHilbertLocalCondition n N S q x}
  map a x hx := by
    obtain ⟨y, hy, _⟩ := (boundedHilbertLocalCondition_iff_lift n N S q x).mp hx
    apply (boundedHilbertLocalCondition_iff_lift n N S q (a.unop ≫ x)).mpr
    have h : (a.unop ≫ y) ≫ Data.GradedHilbert.boundedHilbertParameterOver n N S q = a.unop ≫ x := by
      rw [Category.assoc, hy]
    exact ⟨a.unop ≫ y, h,
      fun z hz => (cancel_mono (Data.GradedHilbert.boundedHilbertParameterOver n N S q)).mp (hz.trans h.symm)⟩

theorem bounded_hilbert_scheme_representation :
    ∃ e : yoneda.obj (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) ≅
        (boundedHilbertSubfunctor (ι := ι) n N S q).toFunctor,
      e.hom ≫ (boundedHilbertSubfunctor (ι := ι) n N S q).ι =
        yoneda.map (Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S q) := by
  apply SubfunctorRepresentations.subfunctor_representation_of_lifts
  intro T x
  change boundedHilbertLocalCondition n N S q x ↔ _
  rw [boundedHilbertLocalCondition_iff_lift]
  constructor
  · rintro ⟨y, hy, _⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy, fun z hz => (cancel_mono (Data.GradedHilbert.boundedHilbertParameterOver n N S q)).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Representation.GradedHilbert
