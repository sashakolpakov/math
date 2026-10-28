import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectiveAmbientNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.DegreeLocus

/-! # Bounded Polynomial Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.BoundedPolynomialFamily.GradedHilbert

noncomputable section

/-! Bounded polynomial parameters give a natural map to the native Hilbert
functor of projective space over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {n : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
variable (q : ℕ → ℕ)

def globalBoundedPolynomialFamily {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T :=
  ProjectiveAmbient.GradedHilbert.polynomialFamilyOverOriginalBase M x (Intrinsic.PolynomialFamily.GradedHilbert.boundedNativePolynomialFamily M g N hg q x hx)

theorem globalBoundedPolynomialFamily_baseChange {T U : Over S} (a : U ⟶ T) (x : T ⟶ M)
    (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    globalBoundedPolynomialFamily M g N hg q (a ≫ x)
        ((Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).map a.op hx) =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a (globalBoundedPolynomialFamily M g N hg q x hx) := by
  dsimp only [globalBoundedPolynomialFamily]
  rw [Intrinsic.PolynomialNaturality.GradedHilbert.boundedNativePolynomialFamily_baseChange, ProjectiveAmbientNaturality.GradedHilbert.polynomialFamilyOverOriginalBase_baseChange]

def boundedPolynomialFamilyTransformation :
    (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).toFunctor ⟶
      Hilbert.Functor.familyFunctor (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) where
  app T := ↾fun x => globalBoundedPolynomialFamily M g N hg q x.val x.property
  naturality T U a := by
    ext x
    exact globalBoundedPolynomialFamily_baseChange M g N hg q a.unop x.val x.property

def boundedHilbertPolynomialFamilyTransformation :
    (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).toFunctor ⟶
      Hilbert.Functor.familyFunctor (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) where
  app T := ↾fun x => globalBoundedPolynomialFamily M g N hg q x.val
    (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q x.val x.property)
  naturality T U a := by
    ext x
    exact globalBoundedPolynomialFamily_baseChange M g N hg q a.unop x.val
      (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q x.val x.property)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.BoundedPolynomialFamily.GradedHilbert
