import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine
import OAI.Geometry.ComplexBall.PrescribedSignsB

/-! # Prescribed Subspace Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrescribedSubspaceTransport

noncomputable section

/-! Paired linear isometries transport the literal prescribed Hodge
summands when they transport the distinguished negative line. -/

open OAI.Geometry.ComplexBall.PrescribedSignsB

theorem prescribed_subspace_transport {I : Type} (B : I → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : I) (d : I → Bool)
    (f k : I → (Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec))
    (hB : ∀ i x y, B i (f i x) (k i y) = B i x y)
    (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart) (c : ℂ) (hc : c ≠ 0) (hl : Geometry.ComplexBall.PrescribedSignsB.lineVector w = c • f μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z))
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient I) (hu : Geometry.ComplexBall.PrescribedSignsB.Prescribed (fun i x y => B i x y) μ d z u) :
    Geometry.ComplexBall.PrescribedSignsB.Prescribed (fun i x y => B i x y) μ d w (fun i => (f i (u i).1, k i (u i).2)) := by
  intro i
  by_cases hi : i = μ
  · subst i
    have h := hu μ
    simp only at h ⊢
    have hs : Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} = (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).map (f μ).toLinearMap := by
      rw [hl, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc), Submodule.map_span, Set.image_singleton]
      rfl
    constructor
    · rw [hs]
      exact ⟨(u μ).1, h.1, rfl⟩
    · rw [hl, map_smul]
      change c * B μ (f μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) (k μ (u μ).2) = 0
      rw [hB, h.2, mul_zero]
  · have h := hu i
    simp only [ite_eq_right hi] at h ⊢
    cases hd : d i
    · simp only [hd, Bool.false_eq_true, ite_false] at h ⊢
      exact (congrArg (k i) h).trans (k i).map_zero
    · simp only [hd, ite_true] at h ⊢
      exact (congrArg (f i) h).trans (f i).map_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrescribedSubspaceTransport
