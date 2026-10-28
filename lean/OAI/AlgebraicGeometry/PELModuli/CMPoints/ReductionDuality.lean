import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityBlockPolarization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

/-! # Reduction Duality -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The actual universal PEL Rosati relation survives the two pullbacks
to every geometric fiber. Hence the conjugate-block pairing theorem
applies to precisely the fibers occurring in the CMPoints statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

theorem Models.RankThreePELModel.GoodIntegralReduction.fiber_rosati (a : M.Family) (x : R.geom a) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (R.fiberPolarized a x) (R.fiberAction a x) := by
  have h := AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation.pullback
    (M.integral a).universal.data.polarized (M.integral a).universal.data.action
    (M.integral a).universal.rosati (R.projection a)
  exact AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation.pullback (R.polarized a) (R.action a) h (R.fiberMap a x)

theorem Models.RankThreePELModel.GoodIntegralReduction.fiber_polarization_duality
    (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
    (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) :
    DualityPairing.PolarizationDuality (R.fiberPolarized a x) (R.fiberAction a x)
      (j.localCharacter M.extendedEmbedding τ)
      (j.localCharacter M.extendedEmbedding (Arithmetic.rationalConjugation E * τ)) := by
  have hgood : q.Coprime (∏ i, (M.datum a).polarizationType i) := by
    exact (R.polarizationPrimeToQ a).of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0))
  exact CartierDualityBlockPolarization.polarizationDuality_of_native_CartierDuality j M.extendedEmbedding hsplit
    (R.fiberPolarized a x) (R.fiberAction a x) (R.fiber_rosati a x) hgood τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
