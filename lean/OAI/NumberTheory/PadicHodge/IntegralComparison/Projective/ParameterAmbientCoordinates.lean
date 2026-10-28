import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterNeighborhood

/-! # Parameter Ambient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAmbientCoordinates

noncomputable section

/-! The ambient map used by the original projective adjunction is
unchanged when expressed in the prescribed parameter basis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial _root_.Module
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

universe u
variable {R : Type u} [CommRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  ParameterNeighborhood.sectionAlgebra

variable (i : Fin (c + g + 1)) (U : (IntrinsicOverlap.Intrinsic.space R (c + g)).Opens)
  (hU : IsAffineOpen U) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (j : Fin (c + g + 1)) (I : Ideal Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U))
  (b : Basis (Fin (c + g)) Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)⁄R])

theorem ambient_eq :
    AmbientAdjunction.ambientIso i U hU hUi j I =
    ParameterLineAdjunction.ambient I b
      ((AffineOpen.InternalHom.sections U hU).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)))
      (AmbientAdjunction.chartLineExterior i U hU hUi j) := by
  unfold AmbientAdjunction.ambientIso ParameterLineAdjunction.ambient
  exact congrArg (fun q =>
    ((AmbientAdjunction.chartLineExterior i U hU hUi j).baseChange
      Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) ⧸ I) _ _).trans q)
    (TopExteriorBaseChange.independent_basis (Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) ⧸ I)
      (AmbientAdjunction.differentialBasis i U hU hUi) b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAmbientCoordinates
