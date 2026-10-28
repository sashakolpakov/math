import OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport

/-! # Paired Symplectic -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PairedSymplectic.Realization

noncomputable section

/-! Explicit symplectic coordinates for paired split blocks with nondegenerate cross-pairings. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {K Place : Type*} [Field K]

abbrev SplitPairedSpace := Place → (Fin 3 → K) × (Fin 3 → K)

def pairedCoordinateEquiv (A : Place → (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    SplitPairedSpace (K := K) (Place := Place) ≃ₗ[K]
      (Sum (Place × Fin 3) (Place × Fin 3) → K) where
  toFun u := Sum.elim (fun p => (u p.1).1 p.2) (fun p => A p.1 (u p.1).2 p.2)
  invFun x τ := (fun i => x (Sum.inl (τ, i)), (A τ).symm (fun i => x (Sum.inr (τ, i))))
  left_inv u := by
    funext τ
    exact Prod.ext rfl ((A τ).symm_apply_apply (u τ).2)
  right_inv x := by
    funext j
    cases j with
    | inl p => rfl
    | inr p => exact congrFun ((A p.1).apply_symm_apply (fun i => x (Sum.inr (p.1, i)))) p.2
  map_add' u v := by
    funext j
    cases j with
    | inl p => rfl
    | inr p => exact congrFun ((A p.1).map_add (u p.1).2 (v p.1).2) p.2
  map_smul' a u := by
    funext j
    cases j with
    | inl p => rfl
    | inr p => exact congrFun ((A p.1).map_smul a (u p.1).2) p.2

def pairedTraceValue [Fintype Place] (T : Place → Matrix (Fin 3) (Fin 3) K)
    (u v : SplitPairedSpace (K := K) (Place := Place)) : K :=
  ∑ τ, ((u τ).1 ⬝ᵥ (T τ *ᵥ (v τ).2) - (v τ).1 ⬝ᵥ (T τ *ᵥ (u τ).2))

def pairedSymplecticCoordinates (T : Place → Matrix (Fin 3) (Fin 3) K)
    (hT : ∀ τ, (T τ).det ≠ 0) :
    SplitPairedSpace (K := K) (Place := Place) ≃ₗ[K]
      (Sum (Place × Fin 3) (Place × Fin 3) → K) :=
  pairedCoordinateEquiv (fun τ => Matrix.toLinearEquiv' (T τ)
    (Matrix.invertibleOfIsUnitDet (T τ) (isUnit_iff_ne_zero.mpr (hT τ))))

theorem pairedSymplecticCoordinates_inl (T : Place → Matrix (Fin 3) (Fin 3) K)
    (hT : ∀ τ, (T τ).det ≠ 0) (u : SplitPairedSpace (K := K) (Place := Place)) (τ : Place) (i : Fin 3) :
    pairedSymplecticCoordinates T hT u (Sum.inl (τ, i)) = (u τ).1 i := rfl

theorem pairedSymplecticCoordinates_inr (T : Place → Matrix (Fin 3) (Fin 3) K)
    (hT : ∀ τ, (T τ).det ≠ 0) (u : SplitPairedSpace (K := K) (Place := Place)) (τ : Place) (i : Fin 3) :
    pairedSymplecticCoordinates T hT u (Sum.inr (τ, i)) = (T τ *ᵥ (u τ).2) i := rfl

theorem pairedSymplecticCoordinates_pairing [Fintype Place]
    (T : Place → Matrix (Fin 3) (Fin 3) K) (hT : ∀ τ, (T τ).det ≠ 0)
    (u v : SplitPairedSpace (K := K) (Place := Place)) :
    FramePositivity.Realization.coordinatePairing (pairedSymplecticCoordinates T hT u) (pairedSymplecticCoordinates T hT v) =
      pairedTraceValue T u v := by
  simp only [FramePositivity.Realization.coordinatePairing, Fintype.sum_prod_type, pairedSymplecticCoordinates_inl,
    pairedSymplecticCoordinates_inr, pairedTraceValue, dotProduct, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem pairedCoordinateEquiv_scalar
    (A : Place → (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (a : Place → K)
    (u : SplitPairedSpace (K := K) (Place := Place)) :
    pairedCoordinateEquiv A (fun τ => (a τ • (u τ).1, (a τ)⁻¹ • (u τ).2)) =
      Sum.elim (fun p => a p.1 * pairedCoordinateEquiv A u (Sum.inl p))
        (fun p => (a p.1)⁻¹ * pairedCoordinateEquiv A u (Sum.inr p)) := by
  funext j
  cases j with
  | inl p => rfl
  | inr p => exact congrFun ((A p.1).map_smul (a p.1)⁻¹ (u p.1).2) p.2

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PairedSymplectic.Realization
