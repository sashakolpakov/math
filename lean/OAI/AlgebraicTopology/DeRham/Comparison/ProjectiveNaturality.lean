import OAI.AlgebraicTopology.DeRham.Comparison.Projective
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps

/-! # Projective Naturality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality.IntegralProjectiveVariety

noncomputable section

/-!
# Naturality of the projective de Rham comparison

Algebraic morphisms induce actual smooth maps of the proved analytic
realizations. Both cochain maps in the comparison span commute with those
pullbacks, hence so does the canonical comparison. Over-isomorphisms
therefore identify the constructions independently of projective embedding.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable {V W T : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- The canonical comparison commutes with every actual algebraic pullback. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality (φ : V.toOver ⟶ W.toOver) (n : ℕ) :
    (W.deRhamBettiIso n).hom ≫ AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ n =
      AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ n ≫ (V.deRhamBettiIso n).hom := by
  exact AlgebraicGeometry.Betti.CohomologySpan.Realization.cohomologySpanIso_naturality
    W.deRhamIntegrationCochain W.bettiRestrictionCochain
    V.deRhamIntegrationCochain V.bettiRestrictionCochain
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamCochainPullback φ)
    (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback V.analyticModel W.analyticModel
      (ModuleCat.of ℂ ℂ) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞))
    (Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map φ))
    (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞)).symm
    (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞)).symm n

/-- The inverse comparison has the same actual pullback naturality. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_inv_naturality (φ : V.toOver ⟶ W.toOver) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ n ≫ (V.deRhamBettiIso n).inv =
      (W.deRhamBettiIso n).inv ≫ AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ n := by
  apply (cancel_epi (W.deRhamBettiIso n).hom).mp
  rw [← Category.assoc, AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_id (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback (𝟙 V.toOver) n = 𝟙 (V.rationalCohomology n) :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) n).map_id _

/-- Composition is the ordinary contravariant singular-cohomology composition. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp (φ : V.toOver ⟶ W.toOver)
    (ψ : W.toOver ⟶ T.toOver) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback (φ ≫ ψ) n =
      AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback ψ n ≫ AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback φ n :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) n).map_comp ψ.op φ.op

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_id (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback (𝟙 V.toOver) n = 𝟙 (V.complexCohomology n) :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) n).map_id _

theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_comp (φ : V.toOver ⟶ W.toOver)
    (ψ : W.toOver ⟶ T.toOver) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback (φ ≫ ψ) n =
      AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback ψ n ≫ AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ n :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) n).map_comp ψ.op φ.op

instance _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_isIso (φ : V.toOver ⟶ W.toOver) [IsIso φ] (n : ℕ) :
    IsIso (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ n) := by
  change IsIso ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) n).map φ.op)
  infer_instance

instance _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_isIso (φ : V.toOver ⟶ W.toOver) [IsIso φ] (n : ℕ) :
    IsIso (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback φ n) := by
  change IsIso ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) n).map φ.op)
  infer_instance

/-- An algebraic isomorphism induces an isomorphism on the actual de Rham
cohomology through its genuine differential-form pullback. -/
instance _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_isIso (φ : V.toOver ⟶ W.toOver) [IsIso φ] (n : ℕ) :
    IsIso (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ n) := by
  have : IsIso (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ n ≫ (V.deRhamBettiIso n).hom) := by
    rw [← AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ n) (V.deRhamBettiIso n).hom

/-- The genuine Betti pullback isomorphism attached to an over-isomorphism. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiIso (e : V.toOver ≅ W.toOver) (n : ℕ) :
    W.complexCohomology n ≅ V.complexCohomology n :=
  asIso (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback e.hom n)

/-- The genuine form pullback isomorphism attached to an over-isomorphism. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamIso (e : V.toOver ≅ W.toOver) (n : ℕ) :
    W.deRhamCohomology n ≅ V.deRhamCohomology n :=
  asIso (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback e.hom n)

/-- The two canonical identifications agree after an algebraic change of
presentation, including a change of projective embedding of the same variety. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_presentation_invariance (e : V.toOver ≅ W.toOver) (n : ℕ) :
    W.deRhamBettiIso n ≪≫ AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiIso e n =
      AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamIso e n ≪≫ V.deRhamBettiIso n := by
  apply Iso.ext
  exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality e.hom n

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality.IntegralProjectiveVariety
