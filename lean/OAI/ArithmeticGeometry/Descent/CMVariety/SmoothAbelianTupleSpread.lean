import OAI.ArithmeticGeometry.Descent.CMVariety.RestrictedTupleComparison
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothTwoStageCoefficients

/-! # Smooth Abelian Tuple Spread -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothAbelianTupleSpread

noncomputable section

/-!
Spread a finite tuple of actual group endomorphisms to a smooth arithmetic
neighborhood over the original affine parameter, retaining the exact
original complex-fiber tuple.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem abelian_endomorphism_tuple_spreads_over_smooth_neighborhood
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Algebra R ℂ] (hR : Function.Injective (algebraMap R ℂ))
    {Index : Type} [Fintype Index] {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (k : AbelianEndomorphism.AbelianEndomorphismTuple Index
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))) :
    ∃ (s t : (Finset ℂ)ᵒᵖ)
      (U : (Spec (CommRingCat.of
        (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t.unop))).Opens),
      IsIntegral U ∧ Smooth (U.ι ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t) ∧
      ∃ (q : Spec (CommRingCat.of ℂ) ⟶ U)
        (hq : q ≫ U.ι = AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t)
        (a : AbelianEndomorphism.AbelianEndomorphismTuple Index ((AbelianEndomorphism.twoStageCoefficientFamily R ℂ A s t).pullback U.ι)),
        AbelianEndomorphism.ConjugateAbelianTuples
          (RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison (AbelianEndomorphism.twoStageCoefficientFamily R ℂ A s t) U.ι q
            (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t) hq
            (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
            (AbelianEndomorphism.twoStageCoefficientComparison R ℂ A s t))
          (a.pullback q) k := by
  obtain ⟨s, t, a, ha⟩ := AbelianEndomorphism.abelian_endomorphism_tuple_spreads R ℂ A k
  obtain ⟨U, hU, hsmooth, q, hq⟩ :=
    SmoothTwoStageCoefficients.Abelian.two_stage_coefficients_have_relative_smooth_neighborhood R hR s t
  refine ⟨s, t, U, hU, hsmooth, q, hq, a.pullback U.ι, ?_⟩
  exact RestrictedTupleComparison.Abelian.restricted_tuple_comparison (AbelianEndomorphism.twoStageCoefficientFamily R ℂ A s t) U.ι q
    (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t) hq
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (AbelianEndomorphism.twoStageCoefficientComparison R ℂ A s t) a k ha

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothAbelianTupleSpread
