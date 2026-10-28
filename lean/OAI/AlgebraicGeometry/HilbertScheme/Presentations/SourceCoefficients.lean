import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FormalCoefficientIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientCoefficientLift

/-! # Source Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SourceCoefficients

noncomputable section

/-! Coefficients on every finite adic quotient reconstruct coefficients
over a complete Noetherian base for a proper source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (R : CommRingCat.{u}) [IsNoetherianRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f]

theorem complete_source_coefficients_of_quotients (I : Ideal R) [IsAdicComplete I R]
    (K : X.IdealSheafData)
    (h : ∀ n : ℕ, ∃ C : Ideal (R ⧸ I ^ n),
      Affine.IdealCoefficientTests.IsAffineIdealCoefficient (CommRingCat.of (R ⧸ I ^ n))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))
        (K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))) C) :
    ∃ J : Ideal R, Affine.IdealCoefficientTests.IsAffineIdealCoefficient R f K J := by
  apply Proper.FormalCoefficientIdeal.proper_formal_coefficient_ideal R f I K
  intro n
  obtain ⟨C, hC⟩ := h n
  have hc := Affine.QuotientCoefficientLift.affine_quotient_coefficient_lift f K
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) Ideal.Quotient.mk_surjective C hC
  refine ⟨C.comap (Ideal.Quotient.mk (I ^ n)), ?_⟩
  simpa only [CommRingCat.hom_ofHom, Ideal.mk_ker] using hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SourceCoefficients
