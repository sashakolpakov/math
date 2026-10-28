import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.SpecializationEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.OverlapCriterion

/-! # Intrinsic Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.IntrinsicFamily.GradedHilbert

noncomputable section

/-! Normalized bounded Hilbert parameters define actual native families.
Their equality on chart overlaps is equality of ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u})

theorem normalizedPolynomial_parameterIdeal {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    Polynomial.ParameterSpecialization.GradedHilbert.parameterHomogeneousIdeal (Normalized.Chart.Grassmannian.normalizedChart a S)
      (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)) x =
        Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.AtlasMaps.Grassmannian.chartMatrix a S x) := by
  let : Algebra Γ((Normalized.Chart.Grassmannian.normalizedChart a S).left, ⊤) Γ(T.left, ⊤) := x.left.appTop.hom.toAlgebra
  change Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Γ(T.left, ⊤))
    (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)) = _
  rw [Normalized.PolynomialTransitions.GradedHilbert.normalizedPolynomialIdeal_baseChange]
  congr 1
  rw [Normalized.AtlasMaps.Grassmannian.chartMatrix, Normalized.Chart.Grassmannian.normalizedChartRepresentation_apply]
  rfl

variable [IsLocallyNoetherian S]

def normalizedHilbertNativeFamily (q : ℕ → ℕ) {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T)) :
    Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T := by
  let : IsLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).hom
  exact Global.BoundedPolynomialFamily.GradedHilbert.globalBoundedPolynomialFamily (Normalized.Chart.Grassmannian.normalizedChart a S) (Chart.GradedHilbert.universalPolynomialGenerators a S) N
    (Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S) q x
      (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat (Normalized.Chart.Grassmannian.normalizedChart a S) (Chart.GradedHilbert.universalPolynomialGenerators a S) N
        (Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S) q x hx)

theorem normalizedHilbertNativeFamily_val (q : ℕ → ℕ) {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T)) :
    (normalizedHilbertNativeFamily a S q x hx).val =
      (Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion T (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.AtlasMaps.Grassmannian.chartMatrix a S x)) (𝟙 T)).ker := by
  let : IsLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).hom
  dsimp only [normalizedHilbertNativeFamily]
  rw [Global.PolynomialInclusion.GradedHilbert.globalBoundedPolynomialFamily_val, Polynomial.SpecializationEmbedding.GradedHilbert.globalPolynomialInclusion_parameter_ker]
  exact congrArg (fun J => (Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion T J (𝟙 T)).ker) (normalizedPolynomial_parameterIdeal a S x)

theorem normalizedHilbertNativeFamily_baseChange (q : ℕ → ℕ) {T U : Over S}
    (f : U ⟶ T) (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T)) :
    normalizedHilbertNativeFamily a S q (f ≫ x) ((Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).map f.op hx) =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) f (normalizedHilbertNativeFamily a S q x hx) := by
  let : IsLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).hom
  exact Global.BoundedPolynomialFamily.GradedHilbert.globalBoundedPolynomialFamily_baseChange (Normalized.Chart.Grassmannian.normalizedChart a S) (Chart.GradedHilbert.universalPolynomialGenerators a S) N
    (Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S) q f x
      (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat (Normalized.Chart.Grassmannian.normalizedChart a S) (Chart.GradedHilbert.universalPolynomialGenerators a S) N
        (Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S) q x hx)

theorem normalizedHilbertNativeFamily_overlap (b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (q : ℕ → ℕ)
    {T : Over S} (f : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S)
    (ha : f ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T))
    (hb : f ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S ∈
      (Chart.GradedHilbert.normalizedHilbertChartSubfunctor b S q).obj (.op T)) :
    normalizedHilbertNativeFamily a S q (f ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S) ha =
      normalizedHilbertNativeFamily b S q
        (f ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S) hb := by
  apply Subtype.ext
  rw [normalizedHilbertNativeFamily_val, normalizedHilbertNativeFamily_val,
    OverlapCriterion.GradedHilbert.normalizedOverlap_polynomialIdeal a b S f]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.IntrinsicFamily.GradedHilbert
