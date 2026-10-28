import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialTransitions
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Parameter
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.FiniteType

/-! # Chart -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.Chart.GradedHilbert

noncomputable section

/-! Constructed bounded Hilbert charts inside the actual normalized
Grassmannian charts, with natural representation on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.FiniteType
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u})

def universalPolynomialGenerators :
    Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ((Normalized.Chart.Grassmannian.normalizedChart a S).left, ⊤) n :=
  Normalized.PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)

theorem universalPolynomialGenerators_homogeneous (j : Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    (universalPolynomialGenerators a S j).IsHomogeneous N :=
  Normalized.PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator_homogeneous a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S) j

def normalizedHilbertChartSubfunctor (q : ℕ → ℕ) : Subfunctor (yoneda.obj (Normalized.Chart.Grassmannian.normalizedChart a S)) :=
  BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor (Normalized.Chart.Grassmannian.normalizedChart a S) (universalPolynomialGenerators a S) N
    (universalPolynomialGenerators_homogeneous a S) q

structure NormalizedHilbertChartModel (q : ℕ → ℕ) where
  carrier : Over S
  inclusion : carrier ⟶ Normalized.Chart.Grassmannian.normalizedChart a S
  immersion : IsImmersion inclusion.left
  quasiCompact : QuasiCompact inclusion.left
  representation : yoneda.obj carrier ≅ (normalizedHilbertChartSubfunctor a S q).toFunctor
  compatibility : representation.hom ≫ (normalizedHilbertChartSubfunctor a S q).ι = yoneda.map inclusion

def normalizedHilbertChartModel (q : ℕ → ℕ) : NormalizedHilbertChartModel a S q := by
  apply Classical.choice
  obtain ⟨Z, j, hj, hqc, e, he⟩ := BoundedHilbert.DegreeLocus.GradedHilbert.bounded_hilbert_degree_locus (Normalized.Chart.Grassmannian.normalizedChart a S)
    (universalPolynomialGenerators a S) N (universalPolynomialGenerators_homogeneous a S) q
  exact ⟨⟨Z, j, hj, hqc, e, he⟩⟩

def normalizedHilbertChart (q : ℕ → ℕ) : Over S := (normalizedHilbertChartModel a S q).carrier

def normalizedHilbertChartInclusion (q : ℕ → ℕ) :
    normalizedHilbertChart a S q ⟶ Normalized.Chart.Grassmannian.normalizedChart a S := (normalizedHilbertChartModel a S q).inclusion

instance normalizedHilbertChartInclusion_isImmersion (q : ℕ → ℕ) :
    IsImmersion (normalizedHilbertChartInclusion a S q).left :=
  (normalizedHilbertChartModel a S q).immersion

instance normalizedHilbertChartInclusion_quasiCompact (q : ℕ → ℕ) :
    QuasiCompact (normalizedHilbertChartInclusion a S q).left :=
  (normalizedHilbertChartModel a S q).quasiCompact

instance normalizedHilbertChartInclusion_mono (q : ℕ → ℕ) :
    Mono (normalizedHilbertChartInclusion a S q) :=
  Over.mono_of_mono_left _

def normalizedHilbertChartRepresentation (q : ℕ → ℕ) :
    yoneda.obj (normalizedHilbertChart a S q) ≅ (normalizedHilbertChartSubfunctor a S q).toFunctor :=
  (normalizedHilbertChartModel a S q).representation

theorem normalizedHilbertChartRepresentation_inclusion (q : ℕ → ℕ) :
    (normalizedHilbertChartRepresentation a S q).hom ≫ (normalizedHilbertChartSubfunctor a S q).ι =
      yoneda.map (normalizedHilbertChartInclusion a S q) :=
  (normalizedHilbertChartModel a S q).compatibility

theorem normalizedHilbertChart_universal_mem (q : ℕ → ℕ) :
    normalizedHilbertChartInclusion a S q ∈
      (normalizedHilbertChartSubfunctor a S q).obj (.op (normalizedHilbertChart a S q)) :=
  (SubfunctorRepresentations.represented_subfunctor_mem _ _ (normalizedHilbertChartRepresentation a S q)
    (normalizedHilbertChartRepresentation_inclusion a S q) _ _).mpr
      ⟨𝟙 _, Category.id_comp _⟩

theorem normalizedHilbertChart_factorization_iff (q : ℕ → ℕ) {T : Over S}
    (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    x ∈ (normalizedHilbertChartSubfunctor a S q).obj (.op T) ↔
      ∃! y : T ⟶ normalizedHilbertChart a S q, y ≫ normalizedHilbertChartInclusion a S q = x := by
  rw [SubfunctorRepresentations.represented_subfunctor_mem _ _ (normalizedHilbertChartRepresentation a S q)
    (normalizedHilbertChartRepresentation_inclusion a S q)]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy, fun z hz => (cancel_mono _).mp (hz.trans hy.symm)⟩
  · rintro ⟨y, hy, _⟩
    exact ⟨y, hy⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.Chart.GradedHilbert
