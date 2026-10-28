import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Weil Conjugated Hom -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilConjugatedHom.CM

noncomputable section

/-! Exact operator and projection identities for conjugating an actual
finite Weil homomorphism by a specified element of its genuine cover. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {I G MpR MpF MpA : Type*} [Fintype I] [DecidableEq I]
  [Group G] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (u : MpF) (r : G →* MpF)

def conjugated : G →* MpF := (MulAut.conj u⁻¹).toMonoidHom.comp r

theorem value (g : G) : conjugated u r g = u⁻¹ * r g * u := by
  change u⁻¹ * r g * u⁻¹⁻¹ = _
  rw [inv_inv]

theorem projection (g : G) : D.finite.project (conjugated u r g) =
    (D.finite.project u)⁻¹ * D.finite.project (r g) * D.finite.project u := by
  change D.finite.project (u⁻¹ * r g * u⁻¹⁻¹) = _
  rw [inv_inv, map_mul, map_mul, map_inv]

theorem action (g : G) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    D.finite.action u (D.finite.action (conjugated u r g) φ) =
      D.finite.action (r g) (D.finite.action u φ) := by
  change D.finite.action u (D.finite.action (u⁻¹ * r g * u⁻¹⁻¹) φ) = _
  rw [inv_inv, map_mul, map_mul, map_inv]
  change D.finite.action u ((D.finite.action u).symm
    (D.finite.action (r g) (D.finite.action u φ))) = _
  rw [LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilConjugatedHom.CM
