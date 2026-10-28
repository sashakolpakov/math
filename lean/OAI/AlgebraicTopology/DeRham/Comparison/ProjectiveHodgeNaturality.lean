import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectivePurePullback

/-! # Projective Hodge Naturality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality.IntegralProjectiveVariety

noncomputable section

/-!
# Algebraic pullback preserves rational Hodge classes

The proof uses the literal pure-form pullback, the canonical integration
comparison, and the actual rational-to-complex coefficient map. In
particular, an over-isomorphism preserves and reflects the condition, so
the resulting Hodge-class predicate is independent of projective embedding.
-/

open _root_.CategoryTheory

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- Algebraic pullback preserves the actual pure Betti subspaces. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace
    (φ : V.toOver ⟶ W.toOver) (p q : ℕ)
    {a : W.complexCohomology (p + q)} (ha : a ∈ W.pureBettiSubspace p q) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ (p + q) a ∈ V.pureBettiSubspace p q := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ (p + q) b,
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_mem_pureDeRhamSubspace φ p q hb, ?_⟩
  exact (ConcreteCategory.congr_hom (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality φ (p + q)) b).symm

/-- The same preservation as an inclusion of actual complex submodules. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.pureBettiSubspace_map_pullback_le (φ : V.toOver ⟶ W.toOver) (p q : ℕ) :
    (W.pureBettiSubspace p q).map (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ (p + q)).hom ≤
      V.pureBettiSubspace p q := by
  rintro _ ⟨a, ha, rfl⟩
  exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace φ p q ha

/-- Rational Hodge classes pull back to rational Hodge classes under actual
algebraic morphisms. No complex-linearity assumption on a supplied map is needed. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback (φ : V.toOver ⟶ W.toOver) (p : ℕ)
    {a : W.rationalCohomology (p + p)} (ha : W.IsRationalHodgeClass p a) :
    V.IsRationalHodgeClass p (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback φ (p + p) a) := by
  have h := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace φ p p ha
  have heq := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomologyInclusion_pullback φ (p + p)) a
  change V.rationalCohomologyInclusion (p + p)
      (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback φ (p + p) a) =
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ (p + p) (W.rationalCohomologyInclusion (p + p) a) at heq
  change V.rationalCohomologyInclusion (p + p)
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback φ (p + p) a) ∈ V.pureBettiSubspace p p
  exact heq.symm ▸ h

/-- An actual algebraic isomorphism preserves and reflects pure Betti type. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace_iff
    (e : V.toOver ≅ W.toOver) (p q : ℕ) (a : W.complexCohomology (p + q)) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback e.hom (p + q) a ∈ V.pureBettiSubspace p q ↔
      a ∈ W.pureBettiSubspace p q := by
  constructor
  · intro h
    have hback := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace e.inv p q h
    have hcomp : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback e.inv (p + q)
        (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback e.hom (p + q) a) = a := by
      calc
        _ = AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback (e.inv ≫ e.hom) (p + q) a :=
          (ConcreteCategory.congr_hom
            (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_comp e.inv e.hom (p + q)) a).symm
        _ = a := by simp only [e.inv_hom_id, AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_id, ModuleCat.id_apply]
    rwa [hcomp] at hback
  · exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace e.hom p q

/-- Rational Hodge type is invariant under an actual change of algebraic
presentation, including a change of projective embedding. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback_iff (e : V.toOver ≅ W.toOver) (p : ℕ)
    (a : W.rationalCohomology (p + p)) :
    V.IsRationalHodgeClass p (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) a) ↔
      W.IsRationalHodgeClass p a := by
  constructor
  · intro h
    have hback := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback e.inv p h
    have hcomp : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.inv (p + p)
        (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) a) = a := by
      calc
        _ = AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback (e.inv ≫ e.hom) (p + p) a :=
          (ConcreteCategory.congr_hom
            (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp e.inv e.hom (p + p)) a).symm
        _ = a := by simp only [e.inv_hom_id, AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_id, ModuleCat.id_apply]
    rwa [hcomp] at hback
  · exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback e.hom p

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality.IntegralProjectiveVariety
