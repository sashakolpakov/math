import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic

/-! # Local Coordinate Entries -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalCoordinateEntries

noncomputable section

/-! Entries of the actual local symplectic coordinate change are images
of fixed algebraic coefficients, independent of the prime and embedding. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
  {Place : Type*} [Fintype Place] [DecidableEq Place]
  (σ : Place → E →ₐ[ℚ] K) (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
  (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))

theorem rationalToSplitCoordinates_rational (x : Fin 3 → E) :
    RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.rationalToSplitCoordinates E K σ hσ θ hθ H hH e
      (fun j => algebraMap ℚ K (e x j)) =
      RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.splitSymplecticCoordinates E K σ hσ θ hθ H hH (fun ρ i => ρ (x i)) := by
  have h := RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates_tmul E K e 1 x
  rw [RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.splitRankThreeBaseChange_tmul_eq, one_smul, one_smul] at h
  change RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.splitSymplecticCoordinates E K σ hσ θ hθ H hH
    ((RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).symm (fun j => algebraMap ℚ K (e x j))) = _
  rw [← h, LinearEquiv.symm_apply_apply]

def splitCoordinateCoefficient (x : Fin 3 → E) (b : Bool) (i : Fin 3) : E :=
  if b then θ * ∑ k, H i k * NumberField.IsCMField.complexConj E (x k) else x i

omit [Algebra E K] [IsScalarTower ℚ E K] [Fintype Place] [DecidableEq Place] in
theorem splitSymplecticCoordinates_rational_entry (x : Fin 3 → E)
    (b : Bool) (τ : Place) (i : Fin 3) :
    RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.splitSymplecticCoordinates E K σ hσ θ hθ H hH (fun ρ j => ρ (x j))
      (if b then Sum.inr (τ, i) else Sum.inl (τ, i)) =
      σ τ (splitCoordinateCoefficient E θ H x b i) := by
  cases b
  · rfl
  · change ((σ τ θ • H.map (σ τ)).mulVec
      (fun k => σ τ (NumberField.IsCMField.complexConj E (x k)))) i = _
    simp only [splitCoordinateCoefficient, ite_true, map_mul, map_sum,
      Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]

theorem localSymplecticChange_rational_entry
    (hθc : NumberField.IsCMField.complexConj E θ = -θ)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) = RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E θ H x y)
    (b : Bool) (τ : Place) (i : Fin 3)
    (j : Sum (Place × Fin 3) (Place × Fin 3)) :
    (RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E K σ hσ θ hθ hθc H hH hHerm e he).val
      (if b then Sum.inr (τ, i) else Sum.inl (τ, i)) j =
        σ τ (splitCoordinateCoefficient E θ H (e.symm (Pi.single j 1)) b i) := by
  change LinearMap.toMatrix' (RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.rationalToSplitCoordinates E K σ hσ θ hθ H hH e).toLinearMap
    (if b then Sum.inr (τ, i) else Sum.inl (τ, i)) j = _
  rw [LinearMap.toMatrix'_apply]
  have hx : (fun k => algebraMap ℚ K (e (e.symm (Pi.single j 1)) k)) = Pi.single j 1 := by
    funext k
    simp only [LinearEquiv.apply_symm_apply, Pi.single_apply]
    split_ifs <;> simp
  have hc := rationalToSplitCoordinates_rational E K σ hσ θ hθ H hH e (e.symm (Pi.single j 1))
  rw [hx] at hc
  exact (congrFun hc (if b then Sum.inr (τ, i) else Sum.inl (τ, i))).trans
    (splitSymplecticCoordinates_rational_entry E K σ hσ θ hθ H hH
      (e.symm (Pi.single j 1)) b τ i)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalCoordinateEntries
