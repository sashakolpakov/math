import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem
import OAI.AlgebraicTopology.Kunneth.PresentationPullbackPurity

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality

noncomputable section

/-!
# Naturality of the canonical Hodge realization

An algebraic map from an integral component lands in an actual target
component. Open-immersion lifting constructs that map, so componentwise
pure-form naturality proves naturality for every smooth projective presentation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct Classical

theorem complexification_pullback {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (n : ℕ)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y n)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) n
        ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f).hom.baseChange ℂ x) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y) n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
    simp only [LinearMap.baseChange_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    exact (congrArg (fun y : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n => z • y)
      (ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality f n) c)).trans
        ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.map_smul z _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem canonicalH1_pullback (hHodgeDecomposition : Mem.HodgeDecompositionInput)
    (P Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : P.toOver ⟶ Q.toOver) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Mem.canonicalH1 hHodgeDecomposition Q) (Mem.canonicalH1 hHodgeDecomposition P)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom := by
  intro x hx
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace P.toOver) 1
    ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom.baseChange ℂ x) ∈ P.pureBettiSubspace 1 0
  rw [complexification_pullback]
  exact AlgebraicTopology.Kunneth.PresentationPullbackPurity.Constructions.presentationPullback_mem_pure P Q f 1 0 _ hx

/-- The componentwise and integral-variety definitions give the same actual pieces. -/
theorem integral_presentation_pure (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    V.presentation.pureBettiSubspace p q = V.pureBettiSubspace p q := by
  ext a
  constructor
  · intro ha
    have h := AlgebraicTopology.Kunneth.PresentationPullbackPurity.Constructions.integralPullback_mem_presentationPure V V.presentation
      (𝟙 V.toOver) p q a ha
    have he : Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + q) (𝟙 V.toOver) a = a :=
      ConcreteCategory.congr_hom
        ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) (p + q)).map_id (Opposite.op V.toOver)) a
    exact he ▸ h
  · intro ha
    apply (V.presentation.mem_pureBettiSubspace_iff p q a).mpr
    intro C
    rw [V.presentation.componentBettiEquiv_apply]
    exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace
      (V.presentation.componentInclusionOver C) p q ha

theorem canonicalH1_integral_holomorphic (hHodgeDecomposition : Mem.HodgeDecompositionInput)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (Mem.canonicalH1 hHodgeDecomposition V.presentation).holomorphic =
      (V.pureBettiSubspace 1 0).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1) := by
  change (V.presentation.pureBettiSubspace 1 0).comap _ = _
  rw [integral_presentation_pure]

theorem canonicalH1_componentRestriction (hHodgeDecomposition : Mem.HodgeDecompositionInput)
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents P.carrier) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Mem.canonicalH1 hHodgeDecomposition P)
      (Mem.canonicalH1 hHodgeDecomposition (P.componentVariety C).presentation) (Mem.componentRestriction P C) := by
  have he : Mem.componentRestriction P C =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (P.componentInclusionOver C)).hom := by
    ext x
    exact P.componentBettiEquiv_apply (ModuleCat.of ℚ ℚ) 1 x C
  rw [he]
  exact canonicalH1_pullback hHodgeDecomposition (P.componentVariety C).presentation P
    (P.componentInclusionOver C)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality
