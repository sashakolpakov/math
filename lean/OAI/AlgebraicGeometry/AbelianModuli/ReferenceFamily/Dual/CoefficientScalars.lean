import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

/-! # Coefficient Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientScalars

noncomputable section

/-! Scalar change of the square-zero coordinate is an actual ring
map, natural in coefficient rings and compatible with native dual scalars. -/

def dualCoefficientScale {R : Type*} [CommRing R] (a : R) : DualNumber R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (a • (LinearMap.id : R →ₗ[R] R))

theorem dualCoefficientScale_fst {R : Type*} [CommRing R] (a : R) (x : DualNumber R) :
    (dualCoefficientScale a x).fst = x.fst := TrivSqZeroExt.fst_map _ x

theorem dualCoefficientScale_snd {R : Type*} [CommRing R] (a : R) (x : DualNumber R) :
    (dualCoefficientScale a x).snd = a * x.snd := TrivSqZeroExt.snd_map _ x

theorem dualCoefficientScale_natural {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : R) (x : DualNumber R) :
    NumberCoefficients.dualNumberRingMap f (dualCoefficientScale a x) = dualCoefficientScale (f a) (NumberCoefficients.dualNumberRingMap f x) := by
  apply TrivSqZeroExt.ext
  · change f (dualCoefficientScale a x).fst = (dualCoefficientScale (f a) (NumberCoefficients.dualNumberRingMap f x)).fst
    rw [dualCoefficientScale_fst, dualCoefficientScale_fst]
    rfl
  · change f (dualCoefficientScale a x).snd = (dualCoefficientScale (f a) (NumberCoefficients.dualNumberRingMap f x)).snd
    rw [dualCoefficientScale_snd, dualCoefficientScale_snd]
    exact map_mul f a x.snd

theorem dualCoefficientScale_complex {R : Type} [CommRing R] [Algebra ℂ R]
    (p : R →ₐ[ℂ] ℂ) (c : ℂ) (x : DualNumber R) :
    NumberCoefficients.dualNumberAlgMap p (dualCoefficientScale (algebraMap ℂ R c) x) =
      LieRanks.dualNumberScale ℂ c (NumberCoefficients.dualNumberAlgMap p x) := by
  apply TrivSqZeroExt.ext
  · change p (dualCoefficientScale (algebraMap ℂ R c) x).fst =
      (LieRanks.dualNumberScale ℂ c (NumberCoefficients.dualNumberAlgMap p x)).fst
    rw [dualCoefficientScale_fst]
    exact (TrivSqZeroExt.fst_map _ (NumberCoefficients.dualNumberAlgMap p x)).symm
  · change p (dualCoefficientScale (algebraMap ℂ R c) x).snd =
      (LieRanks.dualNumberScale ℂ c (NumberCoefficients.dualNumberAlgMap p x)).snd
    rw [dualCoefficientScale_snd]
    have h : (LieRanks.dualNumberScale ℂ c (NumberCoefficients.dualNumberAlgMap p x)).snd = c * (NumberCoefficients.dualNumberAlgMap p x).snd :=
      TrivSqZeroExt.snd_map _ _
    rw [h]
    change p (algebraMap ℂ R c * x.snd) = c * p x.snd
    rw [map_mul, p.commutes]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientScalars
