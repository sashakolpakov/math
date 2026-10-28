import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancedTupleExtension
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothAbelianTupleSpread

/-! # Smooth Enhanced Tuple Spread -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothEnhancedTupleSpread.Abelian

noncomputable section

/-! A smooth arithmetic parameter for the complete original enhanced data
with the additional CM tuple, and an actual enhanced isomorphism on its
original complex fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra R ℂ]
  {g N r m : ℕ} {δ : Fin g → ℕ}

def smoothCoefficientEnhancedComparison
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R)))
    (s t : (Finset ℂ)ᵒᵖ)
    (U : (Spec (CommRingCat.of
      (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t.unop))).Opens)
    (q : Spec (CommRingCat.of ℂ) ⟶ U)
    (hq : q ≫ U.ι = AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t) :
    ModuliObjects.Abelian.EnhancedAbelianIso (((EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R ℂ A s t).pullback U.ι).pullback q)
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) :=
  EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison (EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R ℂ A s t) U.ι q
    (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t) hq
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (EnhancedCoefficientComparisons.Abelian.twoStageEnhancedComparison R ℂ A s t)

theorem smoothCoefficientEnhancedComparison_abelian
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R)))
    (s t : (Finset ℂ)ᵒᵖ)
    (U : (Spec (CommRingCat.of
      (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t.unop))).Opens)
    (q : Spec (CommRingCat.of ℂ) ⟶ U)
    (hq : q ≫ U.ι = AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t) :
    (smoothCoefficientEnhancedComparison R A s t U q hq).polarized.abelian =
      RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison (AbelianEndomorphism.twoStageCoefficientFamily R ℂ A.polarized.abelian s t) U.ι q
        (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t) hq
        (A.polarized.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
        (AbelianEndomorphism.twoStageCoefficientComparison R ℂ A.polarized.abelian s t) :=
  EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison_abelian_of_eq (EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R ℂ A s t) U.ι q
    (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t) hq
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (EnhancedCoefficientComparisons.Abelian.twoStageEnhancedComparison R ℂ A s t)
    (AbelianEndomorphism.twoStageCoefficientComparison R ℂ A.polarized.abelian s t)
    (EnhancedCoefficientComparisons.Abelian.twoStageEnhancedComparison_abelian R ℂ A s t)

theorem enhanced_tuple_spreads_over_smooth_neighborhood
    [IsDomain R] [CharZero R] [IsNoetherianRing R]
    (hR : Function.Injective (algebraMap R ℂ))
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R)))
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m)
      (A.polarized.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))) :
    ∃ (s t : (Finset ℂ)ᵒᵖ)
      (U : (Spec (CommRingCat.of
        (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t.unop))).Opens),
      IsIntegral U ∧ Smooth (U.ι ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t) ∧
      ∃ (q : Spec (CommRingCat.of ℂ) ⟶ U)
        (hq : q ≫ U.ι = AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t)
        (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m)
          ((EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R ℂ A s t).pullback U.ι).polarized.abelian),
        AbelianEndomorphism.ConjugateAbelianTuples (smoothCoefficientEnhancedComparison R A s t U q hq).polarized.abelian
          (a.pullback q) k ∧
        Nonempty (ModuliObjects.Abelian.EnhancedAbelianIso
          ((((EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R ℂ A s t).pullback U.ι).withExtraEndomorphisms a).pullback q)
          ((A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).withExtraEndomorphisms k)) := by
  obtain ⟨s, t, U, hU, hsmooth, q, hq, a, ha⟩ :=
    SmoothAbelianTupleSpread.abelian_endomorphism_tuple_spreads_over_smooth_neighborhood R hR A.polarized.abelian k
  have hconj : AbelianEndomorphism.ConjugateAbelianTuples
      (smoothCoefficientEnhancedComparison R A s t U q hq).polarized.abelian (a.pullback q) k := by
    rw [smoothCoefficientEnhancedComparison_abelian]
    exact ha
  refine ⟨s, t, U, hU, hsmooth, q, hq, a, hconj, ?_⟩
  exact ⟨EnhancedTupleExtension.Abelian.enhancedFiberIsoWithExtraTuple ((EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R ℂ A s t).pullback U.ι) q
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (smoothCoefficientEnhancedComparison R A s t U q hq) a k hconj⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothEnhancedTupleSpread.Abelian
