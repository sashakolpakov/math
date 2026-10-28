import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothCoefficientParameter

/-! # Smooth Two Stage Coefficients -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothTwoStageCoefficients.Abelian

noncomputable section

/-! The actual two-stage endomorphism parameter has a smooth neighborhood
over the original arithmetic parameter, through its evaluation point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

instance finiteCoefficientBaseMap_locallyFinitePresentation
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [IsNoetherianRing R]
    (s : Finset B) : LocallyOfFinitePresentation (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s) := by
  let : Algebra.FinitePresentation R (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

theorem two_stage_coefficients_have_relative_smooth_neighborhood
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Algebra R ℂ] (hR : Function.Injective (algebraMap R ℂ))
    (s t : (Finset ℂ)ᵒᵖ) :
    ∃ U : (Spec (CommRingCat.of
        (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t.unop))).Opens,
      IsIntegral U ∧ Smooth (U.ι ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t) ∧
      ∃ q : Spec (CommRingCat.of ℂ) ⟶ U,
        q ≫ U.ι = AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t := by
  let R₁ := FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop
  let R₂ := FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R₁ ℂ t.unop
  let Z := Spec (CommRingCat.of R₂)
  let p := AbelianCoefficientComparison.coefficientInclusion R₁ ℂ t
  let f := AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t
  let : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  let : LocallyOfFinitePresentation f := by
    dsimp only [f, AbelianEndomorphism.twoStageCoefficientBaseMap]
    infer_instance
  let : CharZero (Spec (CommRingCat.of R)).functionField := SmoothCoefficientParameter.Abelian.affine_functionField_charZero R
  have hp : p (IsLocalRing.closedPoint ℂ) = genericPoint Z :=
    SmoothCoefficientParameter.Abelian.complex_spec_map_genericPoint_of_injective (algebraMap R₂ ℂ) Subtype.val_injective
  have hgeneric : f (genericPoint Z) = genericPoint (Spec (CommRingCat.of R)) := by
    have h := congrArg (fun m : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of R) =>
      m (IsLocalRing.closedPoint ℂ)) (AbelianEndomorphism.twoStageCoefficientInclusion_base R ℂ s t)
    change f (p (IsLocalRing.closedPoint ℂ)) =
      (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))) (IsLocalRing.closedPoint ℂ) at h
    rw [hp, SmoothCoefficientParameter.Abelian.complex_spec_map_genericPoint_of_injective (algebraMap R ℂ) hR] at h
    exact h
  exact RelativeGenericSmooth.Abelian.generic_complex_point_factors_through_relative_smooth_open f hgeneric p hp

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothTwoStageCoefficients.Abelian
