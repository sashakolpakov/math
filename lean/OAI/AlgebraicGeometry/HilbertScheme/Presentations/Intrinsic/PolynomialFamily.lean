import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialAmbient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.RelativeProjectiveFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFinitePresentation

/-! # Polynomial Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialFamily.GradedHilbert

noncomputable section

/-! Bounded polynomial parameters define actual ideal-sheaf points of the
native Hilbert-family functor, on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))

theorem nativePolynomial_isFamily {T : Over S} (x : T ⟶ M)
    [Flat (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x)]
    [LocallyOfFinitePresentation (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x)] :
    Hilbert.Functor.IsFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x).ker := by
  have : Flat (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫
      Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left)) := by
    rw [PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]
    infer_instance
  have : IsProper (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫
      Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left)) := by
    rw [PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]
    infer_instance
  have : LocallyOfFinitePresentation (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫
      Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left)) := by
    rw [PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]
    infer_instance
  exact Closed.ImmersionFamily.Hilbert.closedImmersion_isFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x)

def nativePolynomialFamily {T : Over S} (x : T ⟶ M)
    [Flat (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x)]
    [LocallyOfFinitePresentation (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x)] :
    Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) :=
  ⟨(PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x).ker, nativePolynomial_isFamily M I x⟩

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

def boundedNativePolynomialFamily [IsLocallyNoetherian M.left] (q : ℕ → ℕ)
    {T : Over S} (x : T ⟶ M) (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) := by
  let : Flat (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) x) :=
    Bounded.RelativeProjectiveFlatness.GradedHilbert.bounded_degree_locus_relative_family_flat M g N hg q x hx
  exact nativePolynomialFamily M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) x

theorem boundedNativePolynomialFamily_val [IsLocallyNoetherian M.left] (q : ℕ → ℕ)
    {T : Over S} (x : T ⟶ M) (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    (boundedNativePolynomialFamily M g N hg q x hx).val =
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) x).ker := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialFamily.GradedHilbert
