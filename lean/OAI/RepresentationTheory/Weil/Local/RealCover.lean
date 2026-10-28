import OAI.RepresentationTheory.Weil.Local.GenerationSymplectic
import OAI.RepresentationTheory.Weil.Local.OscillatorProjection

/-! # Real Cover -/

namespace OAI.RepresentationTheory.Weil.Local.RealCover.Construction

noncomputable section

/-! Surjectivity of the intrinsic bare metaplectic projection at a real place. -/

theorem real_metaplecticProjection_surjective_standard (n : ℕ) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter 1)) := by
  apply MonoidHom.range_eq_top.mp
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 ⟨-B.val, B.property.neg⟩
    let w := FourierEquivalence.Construction.realFourierOscillator n
    have h : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter 1) := by
      have hh := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter 1)).Normal).conj_mem
        u.val u.property w⁻¹
      simpa only [inv_inv] using hh
    refine ⟨⟨w⁻¹ * u.val * w, h⟩, ?_⟩
    change OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) (w⁻¹ * u.val * w) = GenerationSymplectic.Construction.upperSymplectic B
    rw [map_mul, map_mul, map_inv]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℝ n B).symm
  · intro B
    exact ⟨QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 B, rfl⟩

end

end OAI.RepresentationTheory.Weil.Local.RealCover.Construction
