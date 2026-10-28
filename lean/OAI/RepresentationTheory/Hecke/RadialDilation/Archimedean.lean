import OAI.RepresentationTheory.Hecke.RadialDilation.Cm
import OAI.Geometry.ComplexBall.PrescribedSignsB

/-! # Archimedean -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.Archimedean.Realization

noncomputable section

/-!
# The central scalar on the actual PrescribedSigns period frames

The norm-one scalar acts on paired embeddings by (a,a⁻¹). We compute its
action on PrescribedSigns's explicit period frames. This computation retains the central
determinant character, which disappears upon restriction to SU in CotangentBundle.
-/

open scoped Classical
open OAI.Geometry.ComplexBall.PrescribedSignsB

def pairedScalar (a : ℂ) (u : Geometry.ComplexBall.PrescribedSignsB.Vec × Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.Vec × Geometry.ComplexBall.PrescribedSignsB.Vec :=
  (a • u.1, a⁻¹ • u.2)

def activeCoordinates (a : ℂ) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.Vec :=
  ![a * v 0, a⁻¹ * v 1, a⁻¹ * v 2]

theorem pairedScalar_preserves_pairing (B : Geometry.ComplexBall.PrescribedSignsB.Bilin) (a : ℂ) (ha : a ≠ 0)
    (u v : Geometry.ComplexBall.PrescribedSignsB.Vec × Geometry.ComplexBall.PrescribedSignsB.Vec) :
    B (pairedScalar a u).1 (pairedScalar a v).2 -
        B (pairedScalar a v).1 (pairedScalar a u).2 =
      B u.1 v.2 - B v.1 u.2 := by
  simp [pairedScalar, map_smul, LinearMap.smul_apply, ha]

theorem scalar_preserves_tracePairing {Place : Type*} [Fintype Place]
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (t a : Place → ℂ) (ha : ∀ τ, a τ ≠ 0)
    (u v : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    Geometry.ComplexBall.PrescribedSignsB.tracePairing (fun τ x y => B τ x y) t
        (fun τ => pairedScalar (a τ) (u τ))
        (fun τ => pairedScalar (a τ) (v τ)) =
      Geometry.ComplexBall.PrescribedSignsB.tracePairing (fun τ x y => B τ x y) t u v := by
  apply Finset.sum_congr rfl
  intro τ _
  rw [pairedScalar_preserves_pairing (B τ) (a τ) (ha τ)]

theorem normOne_conjugate_inverse
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (σ : E →ₐ[ℚ] ℂ) :
    AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ (r : E) = (σ (r : E))⁻¹ := by
  have h := congrArg σ hr
  rw [map_mul, map_one] at h
  have hc : σ (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E)) =
      AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ (r : E) :=
    AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.embedding_conjugation E σ.toRingHom (r : E)
  rw [hc] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The paired action is precisely rational multiplication by r in the
embedding coordinates of PrescribedSigns, not an independently chosen character. -/
theorem embeddingCoordinates_scalar
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    {Place : Type*} (σ : Place → E →ₐ[ℚ] ℂ)
    (x : Fin 3 → E) (τ : Place) :
    Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ (fun j => (r : E) * x j) τ =
      pairedScalar (σ τ (r : E)) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x τ) := by
  ext j <;> simp [Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates, pairedScalar,
    normOne_conjugate_inverse E r hr, map_mul, Pi.smul_apply, smul_eq_mul]

theorem active_frame_scalar (B : Geometry.ComplexBall.PrescribedSignsB.Bilin) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (a : ℂ) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    pairedScalar a (Geometry.ComplexBall.PrescribedSignsB.localFrame B z v) = Geometry.ComplexBall.PrescribedSignsB.localFrame B z (activeCoordinates a v) := by
  ext i <;> simp [pairedScalar, activeCoordinates, Geometry.ComplexBall.PrescribedSignsB.localFrame, smul_add,
    smul_smul, mul_comm, mul_assoc]

def periodWeight {Place : Type*} (μ : Place) (d : Place → Bool)
    (a : Place → ℂ) (τ : Place) (i : Fin 3) : ℂ :=
  if τ = μ then (if i = 0 then a τ else (a τ)⁻¹)
  else if d τ then (a τ)⁻¹ else a τ

theorem place_frame_scalar {Place : Type*}
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (a : Place → ℂ) (τ : Place) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    pairedScalar (a τ) (Geometry.ComplexBall.PrescribedSignsB.placeFrame B μ d z τ v) =
      Geometry.ComplexBall.PrescribedSignsB.placeFrame B μ d z τ (fun i => periodWeight μ d a τ i * v i) := by
  by_cases ht : τ = μ
  · subst τ
    have hw : (fun i => periodWeight μ d a μ i * v i) =
        activeCoordinates (a μ) v := by
      funext i
      fin_cases i <;> simp [periodWeight, activeCoordinates]
    rw [hw]
    simpa [Geometry.ComplexBall.PrescribedSignsB.placeFrame] using active_frame_scalar (B μ) z (a μ) v
  · cases hd : d τ <;>
      simp [Geometry.ComplexBall.PrescribedSignsB.placeFrame, ht, hd, periodWeight, pairedScalar] <;> rfl

theorem global_frame_scalar {Place : Type*}
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (a : Place → ℂ) (v : Place → Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (fun τ => pairedScalar (a τ) (Geometry.ComplexBall.PrescribedSignsB.globalFrame B μ d z v τ)) =
      Geometry.ComplexBall.PrescribedSignsB.globalFrame B μ d z (fun τ i => periodWeight μ d a τ i * v τ i) := by
  funext τ
  exact place_frame_scalar B μ d z a τ (v τ)

/-- The actual scalar matrix in the globally injective period frame. -/
def periodScalarMatrix {Place : Type*} [Fintype Place]
    (μ : Place) (d : Place → Bool) (a : Place → ℂ) :
    Matrix (Place × Fin 3) (Place × Fin 3) ℂ :=
  Matrix.diagonal (fun p => periodWeight μ d a p.1 p.2)

theorem active_weight_product {Place : Type*}
    (μ : Place) (d : Place → Bool) (a : Place → ℂ) (ha : a μ ≠ 0) :
    (∏ i : Fin 3, periodWeight μ d a μ i) = (a μ)⁻¹ := by
  simp [periodWeight, Fin.prod_univ_succ]
  field_simp

theorem compact_weight_product {Place : Type*}
    (μ : Place) (d : Place → Bool) (a : Place → ℂ)
    (τ : Place) (ht : τ ≠ μ) :
    (∏ i : Fin 3, periodWeight μ d a τ i) = a τ ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)) := by
  cases hd : d τ <;>
    simp [periodWeight, ht, hd, AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue, zpow_neg]

/-- Active exponent 1-2=-1 and compact-place exponent -3d, before any
identification with differentials on the ball quotient. -/
theorem periodScalarMatrix_det {Place : Type*} [Fintype Place]
    (μ : Place) (d : Place → Bool) (a : Place → ℂ) (ha : a μ ≠ 0) :
    (periodScalarMatrix μ d a).det =
      (a μ)⁻¹ * ∏ τ ∈ Finset.univ.erase μ, a τ ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)) := by
  rw [periodScalarMatrix, Matrix.det_diagonal, Fintype.prod_prod_type]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ),
    active_weight_product μ d a ha]
  congr 1
  apply Finset.prod_congr rfl
  intro τ ht
  exact compact_weight_product μ d a τ (Finset.ne_of_mem_erase ht)

/-- The projected two-dimensional summand has one further inverse scalar. -/
theorem projected_gradient_weight (a : ℂ) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) (i : Fin 2) :
    activeCoordinates a v i.succ = a⁻¹ * v i.succ := by
  fin_cases i <;> rfl

end

end OAI.RepresentationTheory.Hecke.RadialDilation.Archimedean.Realization
