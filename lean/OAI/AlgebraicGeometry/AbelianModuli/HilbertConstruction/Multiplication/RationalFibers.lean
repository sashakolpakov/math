import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.RationalFiberFiniteMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Quadratic

/-! # Rational Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every rational fiber of positive multiplication on a polarized abelian variety is finite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.multiplication_rationalFiber_isFinite (n : ℕ) (hn : 0 < n)
    (a : Spec (.of K) ⟶ A.abelian.scheme.left) (ha : a ≫ A.abelian.scheme.hom = 𝟙 _) :
    IsFinite (Limits.pullback.snd (A.abelian.multiplication n).left a) := by
  have : IsClosedImmersion (a ≫ A.abelian.scheme.hom) :=
    ha.symm ▸ inferInstanceAs (IsClosedImmersion (𝟙 (Spec (.of K))))
  have : IsClosedImmersion a := IsClosedImmersion.of_comp a A.abelian.scheme.hom
  exact Ample.RationalFiberFiniteMorphism.ample_pullback_rationalFiber_isFinite (A.abelian.multiplication n).left a A.graphBundle
    (A.graphBundle_multiplication_isAmple n hn)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
