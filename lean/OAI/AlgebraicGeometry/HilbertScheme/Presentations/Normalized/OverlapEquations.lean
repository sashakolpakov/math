import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients

/-! # Overlap Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapEquations.Grassmannian

noncomputable section

/-!
Equality of two normalized quotients is a closed matrix condition. The
equations force the relevant pivot to be invertible and recover precisely
the previously constructed transition on the overlap.
-/

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

def quotientCompatibilityEquations (b : ι → ν) (Q K : Matrix ι ν R) : Matrix ι ν R :=
  Q - Matrices.Grassmannian.selectedColumns b Q * K

theorem quotientCompatibility_iff_transition (a b : ι → ν) (Q K : Matrix ι ν R)
    (hQ : Matrices.Grassmannian.IsNormalized a Q) : quotientCompatibilityEquations b Q K = 0 ↔
      IsUnit (Matrices.Grassmannian.selectedColumns b Q).det ∧ K = Matrices.Grassmannian.normalizeColumns b Q := by
  change Q - Matrices.Grassmannian.selectedColumns b Q * K = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    have hunit : IsUnit (Matrices.Grassmannian.selectedColumns b Q).det := by
      apply Matrix.isUnit_det_of_right_inverse
      have hc := congrArg (Matrices.Grassmannian.selectedColumns a) h
      rw [Matrices.Grassmannian.selectedColumns_mul, hQ] at hc
      exact hc.symm
    refine ⟨hunit, ?_⟩
    unfold Matrices.Grassmannian.normalizeColumns
    exact ((congrArg (fun M => (Matrices.Grassmannian.selectedColumns b Q)⁻¹ * M) h).trans
      (Matrix.nonsing_inv_mul_cancel_left _ _ hunit)).symm
  · rintro ⟨hunit, rfl⟩
    exact (Matrix.mul_nonsing_inv_cancel_left (Matrices.Grassmannian.selectedColumns b Q) Q hunit).symm

theorem quotientCompatibility_symm (a b : ι → ν) (Q K : Matrix ι ν R)
    (hQ : Matrices.Grassmannian.IsNormalized a Q) (h : quotientCompatibilityEquations b Q K = 0) :
    quotientCompatibilityEquations a K Q = 0 := by
  obtain ⟨hb, rfl⟩ := (quotientCompatibility_iff_transition a b Q K hQ).mp h
  apply (quotientCompatibility_iff_transition b a _ _ (Matrices.Grassmannian.normalizeColumns_normalized b Q hb)).mpr
  refine ⟨?_, (Matrices.Grassmannian.normalizeColumns_inverse a b Q hQ hb).symm⟩
  apply (Matrices.Grassmannian.normalizeColumns_pivot_isUnit_iff a b Q hb).mpr
  rw [hQ, Matrix.det_one]
  exact isUnit_one

omit [DecidableEq ι] in
theorem quotientCompatibility_map {S : Type*} [CommRing S] (φ : R →+* S)
    (b : ι → ν) (Q K : Matrix ι ν R) :
    quotientCompatibilityEquations b (Q.map φ) (K.map φ) =
      (quotientCompatibilityEquations b Q K).map φ := by
  unfold quotientCompatibilityEquations
  rw [Matrices.Grassmannian.selectedColumns_map, ← Matrix.map_mul]
  ext i j
  exact (map_sub φ _ _).symm

variable [Fintype ν] [DecidableEq ν]

theorem quotientCompatibility_iff_kernel_eq (a b : ι → ν) (Q K : Matrix ι ν R)
    (hQ : Matrices.Grassmannian.IsNormalized a Q) (hK : Matrices.Grassmannian.IsNormalized b K) :
    quotientCompatibilityEquations b Q K = 0 ↔ (Matrix.toLin' Q).ker = (Matrix.toLin' K).ker := by
  constructor
  · intro h
    have h' := quotientCompatibility_symm a b Q K hQ h
    have hQK : Q = Matrices.Grassmannian.selectedColumns b Q * K := sub_eq_zero.mp h
    have hKQ : K = Matrices.Grassmannian.selectedColumns a K * Q := sub_eq_zero.mp h'
    apply le_antisymm
    · intro x hx
      change Matrix.toLin' K x = 0
      rw [hKQ, Matrix.toLin'_mul, LinearMap.comp_apply, hx, map_zero]
    · intro x hx
      change Matrix.toLin' Q x = 0
      rw [hQK, Matrix.toLin'_mul, LinearMap.comp_apply, hx, map_zero]
  · intro hker
    apply sub_eq_zero.mpr
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, ← Quotients.Grassmannian.matrix_comp_selectedBasisMap]
    apply LinearMap.ext
    intro x
    have hx : x - Quotients.Grassmannian.selectedBasisMap b (Matrix.toLin' K x) ∈ (Matrix.toLin' K).ker := by
      change Matrix.toLin' K (x - Quotients.Grassmannian.selectedBasisMap b (Matrix.toLin' K x)) = 0
      rw [map_sub, Quotients.Grassmannian.normalizedMatrix_section b K hK, sub_self]
    rw [← hker] at hx
    change Matrix.toLin' Q (x - Quotients.Grassmannian.selectedBasisMap b (Matrix.toLin' K x)) = 0 at hx
    rw [map_sub, sub_eq_zero] at hx
    exact hx

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapEquations.Grassmannian
