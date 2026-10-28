import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation

/-! # Chart Overlap Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartOverlapEvaluation

noncomputable section

/-! Evaluation of homogeneous fractions agrees on intersections of
basic projective opens, represented by a product denominator. -/
universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type v} [CommRing A]

theorem homogeneousAwayEvaluation_awayMap
    (g : ℕ → Submodule R S) [GradedAlgebra g] (f h x : S) {e : ℕ} (hh : h ∈ g e)
    (hx : x = f * h) (φ : S →+* A) (hf : IsUnit (φ f)) (hxunit : IsUnit (φ x)) :
    (AwayEvaluation.homogeneousAwayEvaluation g x φ hxunit).comp (HomogeneousLocalization.awayMap g hh hx) =
      AwayEvaluation.homogeneousAwayEvaluation g f φ hf := by
  let ex : Localization.Away x →+* A := Localization.awayLift φ x hxunit
  let ef : Localization.Away f →+* A := Localization.awayLift φ f hf
  have hfx : IsUnit (algebraMap S (Localization.Away x) f) :=
    isUnit_of_dvd_unit (map_dvd _ ⟨h, hx⟩) (IsLocalization.Away.algebraMap_isUnit x)
  let p : Localization.Away f →+* Localization.Away x :=
    Localization.awayLift (algebraMap S (Localization.Away x)) f hfx
  have hp : ex.comp p = ef := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro s
    have hpS : p (algebraMap S (Localization.Away f) s) = algebraMap S (Localization.Away x) s :=
      IsLocalization.Away.lift_eq (S := Localization.Away f)
        (g := algebraMap S (Localization.Away x)) f hfx s
    have hxS : ex (algebraMap S (Localization.Away x) s) = φ s :=
      IsLocalization.Away.lift_eq (S := Localization.Away x) (g := φ) x hxunit s
    have hfS : ef (algebraMap S (Localization.Away f) s) = φ s :=
      IsLocalization.Away.lift_eq (S := Localization.Away f) (g := φ) f hf s
    exact (congrArg ex hpS).trans (hxS.trans hfS.symm)
  apply RingHom.ext
  intro z
  change ex (HomogeneousLocalization.awayMap g hh hx z).val = ef z.val
  exact (congrArg ex (HomogeneousLocalization.val_awayMap g hh hx z)).trans
    (RingHom.congr_fun hp z.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartOverlapEvaluation
