import OAI.RepresentationTheory.Theta.Adelic.RealNormGaussian
import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport
import OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification

/-! # Local Norm Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalNormCharacter

noncomputable section

/-! Continuous quadratic norm characters on all local fields, including
both archimedean types and split quadratic algebras. -/

open OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport

theorem normSign_real_mul (d : ℝ) (hd : d ≠ 0) (a b : ℝˣ) :
    QuadraticNormCharacter.normSign d (a * b) = QuadraticNormCharacter.normSign d a * QuadraticNormCharacter.normSign d b := by
  rcases lt_or_gt_of_ne hd with hd | hd
  · simp only [RealNormGaussian.normSign_real d hd, Units.val_mul]
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha <;>
      rcases lt_or_gt_of_ne b.ne_zero with hb | hb
    · simp [ha.not_gt, hb.not_gt, mul_pos_of_neg_of_neg ha hb]
    · simp [ha.not_gt, hb, (mul_neg_of_neg_of_pos ha hb).not_gt]
    · simp [ha, hb.not_gt, (mul_neg_of_pos_of_neg ha hb).not_gt]
    · simp [ha, hb, mul_pos ha hb]
  · have hsq : IsSquare d := ⟨Real.sqrt d, by rw [← pow_two, Real.sq_sqrt hd.le]⟩
    rw [QuadraticNormCharacter.normSign_split d hd.ne' hsq, QuadraticNormCharacter.normSign_split d hd.ne' hsq,
      QuadraticNormCharacter.normSign_split d hd.ne' hsq, one_mul]

theorem normSign_complex (d : ℂ) (hd : d ≠ 0) (a : ℂˣ) : QuadraticNormCharacter.normSign d a = 1 := by
  apply QuadraticNormCharacter.normSign_split d hd _ a
  refine ⟨d ^ (1 / 2 : ℂ), ?_⟩
  rw [← pow_two]
  simp [one_div]

theorem normSign_mul
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    (hnd : ¬ DiscreteTopology k) (d : k) (hd : d ≠ 0) (a b : kˣ) :
    QuadraticNormCharacter.normSign d (a * b) = QuadraticNormCharacter.normSign d a * QuadraticNormCharacter.normSign d b := by
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    exact QuadraticNormCharacter.normSign_mul d hd hnd a b
  · rcases Weil.Local.ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, _, _⟩ | ⟨e, _, _⟩
    · rw [← QuadraticNormTransport.normSign_map e d (a * b), ← QuadraticNormTransport.normSign_map e d a, ← QuadraticNormTransport.normSign_map e d b, map_mul]
      exact normSign_real_mul (e d) ((map_ne_zero e).mpr hd) _ _
    · rw [← QuadraticNormTransport.normSign_map e d (a * b), ← QuadraticNormTransport.normSign_map e d a, ← QuadraticNormTransport.normSign_map e d b,
        normSign_complex (e d) ((map_ne_zero e).mpr hd),
        normSign_complex (e d) ((map_ne_zero e).mpr hd),
        normSign_complex (e d) ((map_ne_zero e).mpr hd), one_mul]

def localNormCharacter
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    (hnd : ¬ DiscreteTopology k) (d : k) (hd : d ≠ 0) : kˣ →ₜ* Circle where
  toFun := QuadraticNormCharacter.normSign d
  map_one' := QuadraticNormCharacter.normSign_one d
  map_mul' := normSign_mul hnd d hd
  continuous_toFun := QuadraticNormCharacter.normSign_continuous d hnd

end

end OAI.RepresentationTheory.Theta.Adelic.LocalNormCharacter
