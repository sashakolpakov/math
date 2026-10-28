import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacterNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectivePresentationMorphism
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit

/-! # Compatibility -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Compatibility

noncomputable section

/-! The actual finite H¹ overlap characters commute with reduction of
coefficients and the geometric multiplication-cover refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

theorem overlap_transition (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ (n + 1) A.left).H 1) :
    (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left).hom.app
      (op (MultiplicationCoverCharacter.overlap ℓ (n + 1) A hℓ)) (MultiplicationCoverCharacter.character ℓ (n + 1) A hℓ x) =
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map
      (MultiplicationCoverRefinement.overlapMap ℓ n A hℓ).op
        (MultiplicationCoverCharacter.character ℓ n A hℓ
          (Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1 x)) := by
  let S := Finite.CoverCharacter.presentation ℓ (n + 1) A.left
  let T := Finite.CoverCharacter.presentation ℓ n A.left
  let hS := Finite.CoverCharacter.presentation_shortExact ℓ (n + 1) (X := A.left)
  let hT := Finite.CoverCharacter.presentation_shortExact ℓ n (X := A.left)
  let α := AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left
  obtain ⟨φ, hφ⟩ := InjectivePresentationMorphism.exists_morphism hS (T := T) α
  let U := MultiplicationCoverCharacter.cover ℓ (n + 1) A hℓ
  let D := MultiplicationCoverCharacter.overlap ℓ (n + 1) A hℓ
  let V := MultiplicationCoverCharacter.cover ℓ n A hℓ
  let E := MultiplicationCoverCharacter.overlap ℓ n A hℓ
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let : PreconnectedSpace U.left := inferInstanceAs (PreconnectedSpace A.left)
  let : PreconnectedSpace V.left := inferInstanceAs (PreconnectedSpace A.left)
  let hSlift := Finite.CoverFiniteness.presentation_local_lifts ℓ (n + 1)
    S.X₂ S.X₃ S.f S.g S.zero hS U
      (GroupLaw.multiplication_pow_pullback_zero ℓ (n + 1) A)
  let hTlift := Finite.CoverFiniteness.presentation_local_lifts ℓ n
    T.X₂ T.X₃ T.f T.g T.zero hT V
      (GroupLaw.multiplication_pow_pullback_zero ℓ n A)
  have he := CoverCharacterNaturality.character_refinement_square hS hT φ U D V E
    (MultiplicationCoverCharacter.first ℓ (n + 1) A hℓ) (MultiplicationCoverCharacter.second ℓ (n + 1) A hℓ) (MultiplicationCoverCharacter.first ℓ n A hℓ) (MultiplicationCoverCharacter.second ℓ n A hℓ)
    hSlift hTlift (Finite.CoverCharacter.coefficient_restrictions_eq ℓ (n + 1) _ _)
    (Finite.CoverCharacter.coefficient_restrictions_eq ℓ n _ _)
    (MultiplicationCoverRefinement.coverMap ℓ n A hℓ)
    (MultiplicationCoverRefinement.overlapMap ℓ n A hℓ)
    (MultiplicationCoverRefinement.overlapMap_first ℓ n A hℓ)
    (MultiplicationCoverRefinement.overlapMap_second ℓ n A hℓ)
    (Finite.CoverCharacter.coefficient_restrictions_eq ℓ n _ _) x
  rw [hφ] at he
  exact he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Compatibility
