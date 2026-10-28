import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCochainNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ZeroCocycles

/-! # Rational Smooth Cochains -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCochains.CM.Construction

noncomputable section

/-! The literal rational coefficient inclusion followed by restriction
to smooth simplices, with differential, pullback, and point formulas. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def rationalSmoothCochain (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).X n) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X n :=
  (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f n
    ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of M)).f n c)

theorem rationalSmoothCochain_d (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).X n) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d n (n + 1)
      (rationalSmoothCochain E M n c) = rationalSmoothCochain E M (n + 1)
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).d n (n + 1) c) := by
  let rc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of M)).X n :=
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of M)).f n c
  let dc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).X (n + 1) :=
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).d n (n + 1) c
  let rc' : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of M)).X (n + 1) :=
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of M)).f (n + 1) dc
  have h₁ : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d n (n + 1)
      ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f n rc) =
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f (n + 1)
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of M)).d n (n + 1) rc) :=
    ConcreteCategory.congr_hom
      ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).comm n (n + 1)) rc
  have h₂ : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of M)).d n (n + 1) rc =
      rc' :=
    ConcreteCategory.congr_hom ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of M)).comm n (n + 1)) c
  exact h₁.trans (congrArg (fun w :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of M)).X (n + 1) =>
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f (n + 1) w) h₂)

theorem rationalSmoothCochain_point
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).X 0) (x : M) :
    ZeroCocycles.CM.Construction.smoothZeroCochainPoint E M (rationalSmoothCochain E M 0 c) x =
      ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) (TopCat.of M)).hom c x : ℂ) := by
  exact (ZeroCocycles.CM.Construction.smoothZeroCochainPoint_restriction E M
    ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of M)).f 0 c) x).trans
      (RationalCochainNaturality.CM.Construction.rationalToComplexCochain_point (TopCat.of M) c x)

variable {E M}
  {F N : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N]

theorem rationalSmoothCochain_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of N)).X n) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F (ModuleCat.of ℂ ℂ) f hf).f n
      (rationalSmoothCochain F N n c) =
    rationalSmoothCochain E M n
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (TopCat.ofHom ⟨f, hf.continuous⟩)).f n c) := by
  let rc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of N)).X n :=
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of N)).f n c
  have h₁ := ConcreteCategory.congr_hom (congrArg (fun k => k.f n)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ) f hf)) rc
  have h₂ := RationalCochainNaturality.CM.Construction.rationalToComplexCochain_pullback (TopCat.ofHom ⟨f, hf.continuous⟩) n c
  exact h₁.symm.trans (congrArg
    ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f n) h₂)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCochains.CM.Construction
