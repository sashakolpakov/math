import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedGeneratorFamily
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientBaseChange

/-! # Weighted Family Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedFamilyNaturality.Construction

noncomputable section

/-! Fixed normal coefficient families commute with every derivative-preserving refinement. -/

variable {k l R V ι : Type*} [CommRing k] [CommRing l] [CommRing R] [CommRing V]
  [Algebra k R] [Algebra l V]
  (D : Derivation k R R) (E : Derivation l V V) (g : R →+* V)
  (hD : ∀ x : R, E (g x) = g (D x))

include hD in
theorem iterated_derivation_intertwines (n : ℕ) (x : R) : E^[n] (g x) = g (D^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hD]

include hD in
/-- Each coefficient ideal of the same indexed family maps exactly to its
coefficient ideal on the refined chart. -/
theorem coordinateDerivativeFamilyIdeal_map (z : R) (p : ι → R) (n : ℕ) :
    (HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p n).map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap g z) =
      HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal E (g z) (fun t => g (p t)) n := by
  rw [HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext t
  change Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap g z (Ideal.Quotient.mk _ (D^[n] (p t))) = _
  rw [Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk (Ideal.span {g z}))
    (iterated_derivation_intertwines D E g hD n (p t)).symm

include hD in
/-- Weighting does not change this exact compatibility, and no family
generators or coefficient equations have to be reselected. -/
theorem weightedCoordinateDerivativeFamilyIdeal_map (z : R) (p : ι → R) (b : ℕ) :
    (WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b).map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap g z) =
      WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal E (g z) (fun t => g (p t)) b := by
  unfold WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  apply congrArg (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b)
  funext j
  exact coordinateDerivativeFamilyIdeal_map D E g hD z p j.val

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedFamilyNaturality.Construction
