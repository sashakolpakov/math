import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CenterPreimage
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicCoefficientCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.PersistentCoefficientStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Tangent Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.TangentCenter.Construction

noncomputable section

/-! Intrinsic coefficient tangent centers agree with the actual lifted étale-line centers. -/

open _root_.Polynomial

universe u

variable (k : Type u) {H R : Type u}
    [Field k] [CommRing H] [CommRing R]
    [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
    [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Smooth k H]

theorem etaleLine_tangent_center_eq_preimage
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X})) (ℓ : ℕ) :
    Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom) ℓ) =
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C ℓ).comap
        (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X})) := by
  let eₖ := e.restrictScalars k
  let : Algebra.Smooth k (R ⧸ Ideal.span {algebraMap H[X] R X}) := Algebra.Smooth.of_equiv eₖ.symm
  have hm := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k eₖ.toAlgHom
    (RingHom.Etale.of_bijective e.bijective) C ℓ
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C ℓ).map e.toRingHom =
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom) ℓ at hm
  rw [← hm]
  exact CenterPreimage.Construction.etaleLineCenter_eq_quotient_preimage e (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C ℓ)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.TangentCenter.Construction
