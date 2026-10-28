import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricOpen
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Geometric Modification Integral -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricModificationIntegral

noncomputable section

/-! An integral proper modification that is an isomorphism over a
nonempty open of a geometrically integral scheme is geometrically integral. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.GeometricModification

variable {K : Type u} [Field K] {X Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of K)) [IsProper f] [GeometricallyIntegral f]
variable (q : Z ⟶ X) [IsProper q] [Surjective q] [IsIntegral Z]
variable (U : X.Opens) [hU : Nonempty U] [hiso : IsIso (q ∣_ U)]

include U hU hiso

theorem geometricallyIntegral : GeometricallyIntegral (q ≫ f) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (q ≫ f)
  have : Nonempty (q ⁻¹ᵁ U).toScheme := by
    let x : U := Classical.choice hU
    obtain ⟨z, hz⟩ := q.surjective x.1
    exact ⟨⟨z, (show q z ∈ U from hz.symm ▸ x.2)⟩⟩
  have : GeometricallyIntegral (U.ι ≫ f) := GeometricOpen.Construction.GeometricOpenSubset.geometricallyIntegral f U
  have : GeometricallyIntegral ((q ⁻¹ᵁ U).ι ≫ (q ≫ f)) := by
    rw [← morphismRestrict_ι_assoc]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral
      (q ∣_ U) (U.ι ≫ f)).mpr inferInstance
  exact GeometricDense.Construction.GeometricDenseOpen.geometricallyIntegral (q ≫ f) (q ⁻¹ᵁ U)

end Construction.GeometricModification

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricModificationIntegral
