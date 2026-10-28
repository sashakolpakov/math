import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Fractions

/-! # Overlap Rings -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapRings

noncomputable section

/-! Compatibility of projective-coordinate evaluations on overlaps of standard charts. -/

universe u

variable {R B : Type u} [CommRing R] [CommRing B] {n : ℕ}

/-- Evaluation commutes with passing from a homogeneous denominator to a product denominator. -/
theorem homogeneousFractionEvaluation_awayMap (c : R →+* B) (v : Fin (n + 1) → B)
    (f g x : Projective.ProjectivePresentations.coordinateRing R n) (e : ℕ) (hg : g ∈ Projective.ProjectivePresentations.coordinateGrading R n e)
    (hx : x = f * g) (hf : IsUnit (MvPolynomial.eval₂Hom c v f))
    (hxu : IsUnit (MvPolynomial.eval₂Hom c v x)) :
    (Homogeneous.Fractions.homogeneousFractionEvaluation c v x hxu).comp
        (HomogeneousLocalization.awayMap (Projective.ProjectivePresentations.coordinateGrading R n) hg hx) =
      Homogeneous.Fractions.homogeneousFractionEvaluation c v f hf := by
  let ev := MvPolynomial.eval₂Hom c v
  let ex : Localization.Away x →+* B := Localization.awayLift ev x hxu
  let ef : Localization.Away f →+* B := Localization.awayLift ev f hf
  have hfx : IsUnit (algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away x) f) :=
    isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩) (IsLocalization.Away.algebraMap_isUnit x)
  let p : Localization.Away f →+* Localization.Away x :=
    Localization.awayLift (algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away x)) f hfx
  have hp : ex.comp p = ef := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro a
    have hpA : p (algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away f) a) =
        algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away x) a :=
      IsLocalization.Away.lift_eq (S := Localization.Away f)
        (g := algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away x)) f hfx a
    have hxA : ex (algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away x) a) = ev a :=
      IsLocalization.Away.lift_eq (S := Localization.Away x) (g := ev) x hxu a
    have hfA : ef (algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away f) a) = ev a :=
      IsLocalization.Away.lift_eq (S := Localization.Away f) (g := ev) f hf a
    exact (congrArg ex hpA).trans (hxA.trans hfA.symm)
  apply RingHom.ext
  intro z
  change ex (HomogeneousLocalization.awayMap (Projective.ProjectivePresentations.coordinateGrading R n) hg hx z).val = ef z.val
  exact (congrArg ex (HomogeneousLocalization.val_awayMap (Projective.ProjectivePresentations.coordinateGrading R n) hg hx z)).trans
    (RingHom.congr_fun hp z.val)

/-- Dividing all coordinates by the unit value of the jth coordinate normalizes that coordinate. -/
theorem normalizedCoordinate_eq_one (v : Fin (n + 1) → B) (j : Fin (n + 1))
    (a : Bˣ) (ha : v j = a) : (↑a⁻¹ : B) * v j = 1 := by
  rw [ha]
  exact a.inv_mul

/-- Evaluating fractions in the jth chart agrees with evaluating the normalized coordinates. -/
theorem homogeneousFractionEvaluation_normalized (c : R →+* B) (v : Fin (n + 1) → B)
    (j : Fin (n + 1)) (a : Bˣ) (ha : v j = a)
    (hj : IsUnit (MvPolynomial.eval₂Hom c v (MvPolynomial.X j))) :
    Homogeneous.Fractions.homogeneousFractionEvaluation c v (MvPolynomial.X j) hj =
      ProjectiveChart.Evaluation.projectiveChartEvaluation c (fun k => (↑a⁻¹ : B) * v k) j (normalizedCoordinate_eq_one v j a ha) := by
  have hv : MvPolynomial.eval₂Hom c v (MvPolynomial.X j) * (↑a⁻¹ : B) = 1 :=
    (congrArg (fun z : B => z * (↑a⁻¹ : B)) ((MvPolynomial.eval₂Hom_X' c v j).trans ha)).trans a.mul_inv
  apply RingHom.ext
  intro z
  obtain ⟨d, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.isHomogeneous_X R j) z
  have hp' : p ∈ Projective.ProjectivePresentations.coordinateGrading R n d := by simpa only [smul_eq_mul, mul_one] using hp
  exact (Homogeneous.Fractions.homogeneousFractionEvaluation_mk c v (MvPolynomial.X j) hj 1
    (MvPolynomial.isHomogeneous_X R j) d p hp (↑a⁻¹ : B) hv).trans
      ((mul_comm _ _).trans
        ((Homogeneous.Evaluation.homogeneousEvaluation_normalize c v a p d hp').symm.trans
          (ProjectiveChart.Evaluation.projectiveChartEvaluation_mk c (fun k => (↑a⁻¹ : B) * v k) j
            (normalizedCoordinate_eq_one v j a ha) d p hp').symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapRings
