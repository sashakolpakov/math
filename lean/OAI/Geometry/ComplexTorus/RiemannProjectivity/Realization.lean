import OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Realization -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.Realization

noncomputable section

/-!
# RiemannProjectivity: the manuscript's exact CM sign-type realization theorem

The CM trace polarization and full period lattice give a projective analytic
torus by the proved RiemannProjectivity criterion. Homogeneous cone equations construct its
reduced projective closure; local polynomial equations prove native algebraic
smoothness. Algebraizing the addition and inverse graphs supplies actual
commutative group-scheme operations. The trace comparison on lattice loops,
simplex integration, and the complex diffeomorphism with the native scheme
points identify rational H¹ and both prescribed Hodge subspaces.

`Realization` isolates RiemannProjectivity as the sole named input. This file discharges
that input with its proved theorem and retains the specification's exact type.
-/

namespace Constructions

theorem riemannProjectivityInput_proved : Fin.Constructions.RiemannProjectivityInput := by
  intro V _ _ _ Λ _ _
  exact ProjectivityCriterion.riemann_projectivity_criterion V Λ

end Constructions

namespace CM

/-- Every odd CM sign type is realized by the genuine rational H¹ of an
actual complex abelian variety, with both native Hodge types respected. -/
theorem realization_of_cm_sign_type
    (E : IntermediateField ℚ ℂ)
    [NumberField E]
    [IsGalois ℚ E]
    [NumberField.IsCMField E]
    (v : Gal(E/ℚ) → Bool)
    (hv : ∀ τ : Gal(E/ℚ), v (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !(v τ)) :
    Nonempty (AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM.HodgeRealization (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E ⟨v, hv⟩)) :=
  IntrinsicComparison.Constructions.realization_of_cm_sign_type
    Constructions.riemannProjectivityInput_proved E v hv

end CM

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.Realization
