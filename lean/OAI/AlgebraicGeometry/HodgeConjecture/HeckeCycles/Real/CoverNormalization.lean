import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.RealCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum

/-! # Cover Normalization -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CoverNormalization.CM.VacuumGraph

/-! The constructed vacuum is the actual standard positive-frame
Gaussian. LocalWeil's proved Gaussian graph determines its transformed
coefficient, before comparing coordinate determinants. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum.CM

theorem standard_quadratic (n : ℕ) :
    (RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).quadraticMatrix = Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  change (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) * (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ = _
  rw [inv_one, Matrix.mul_one]

theorem vacuum_gaussian (n : ℕ) (x : Fin n → ℝ) :
    (Constructed.Vacuum.CM.vacuum (Fin n)).val x = RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian (RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).quadraticMatrix x := by
  rw [Constructed.Vacuum.CM.vacuum_apply, standard_quadratic, RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul]
  congr 1
  change -((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2) =
    (Real.pi : ℂ) * Complex.I * (Complex.I * ∑ i, (x i : ℂ) * (x i : ℂ))
  simp only [← pow_two]
  linear_combination -(Real.pi : ℂ) * (∑ i, (x i : ℂ) ^ 2) * Complex.I_sq

theorem vacuum_toL2 (n : ℕ) :
    RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2 ℝ n (SchwartzComparison.CM.tests n (Constructed.Vacuum.CM.vacuum (Fin n))) = (RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).gaussianLp := by
  apply (MemLp.toLp_eq_toLp_iff (RepresentationTheory.Weil.Local.UnitaryInner.Construction.test_memLp_two ℝ n (SchwartzComparison.CM.tests n (Constructed.Vacuum.CM.vacuum (Fin n))))
    (RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).gaussian_memLp).mpr
  exact Filter.Eventually.of_forall (vacuum_gaussian n)

theorem transformed_vacuum_amplitude (n : ℕ) (g : SchrodingerAction.CM.RealMp n) :
    ∃ c : ℂ,
      c ^ 2 * ((RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).act (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)).position.det = 1 ∧
      ∀ x : Fin n → ℝ, (SchrodingerAction.CM.action n g (Constructed.Vacuum.CM.vacuum (Fin n))).val x =
        c * RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian
          ((RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).act (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)).quadraticMatrix x := by
  let P := RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n
  have hin : RepresentationTheory.Weil.Local.FrameGaussianAction.Construction.realGaussianGraph P P.gaussianLp :=
    ⟨1, by change 1 ^ 2 * (1 : Matrix (Fin n) (Fin n) ℂ).det = 1; simp, by rw [one_smul]⟩
  have hgraph := RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction.real_standard_metaplectic_le_gaussianSubgroup n g.property
  obtain ⟨c, hc, he⟩ := (hgraph P P.gaussianLp).mp hin
  refine ⟨c, hc, ?_⟩
  rw [← vacuum_toL2, RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator_apply] at he
  let Q := P.act (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)
  have ha : (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g (SchwartzComparison.CM.tests n (Constructed.Vacuum.CM.vacuum (Fin n)))).val =ᵐ[
      RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n] fun x => c * RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian Q.quadraticMatrix x :=
    (MemLp.toLp_eq_toLp_iff
      (RepresentationTheory.Weil.Local.UnitaryInner.Construction.test_memLp_two ℝ n (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g (SchwartzComparison.CM.tests n (Constructed.Vacuum.CM.vacuum (Fin n)))))
      (Q.gaussian_memLp.const_smul c)).mp he
  have hf := Measure.eq_of_ae_eq ha
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat_continuous (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g (SchwartzComparison.CM.tests n (Constructed.Vacuum.CM.vacuum (Fin n)))).property)
    (continuous_const.mul (RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian_continuous _))
  exact congrFun hf

theorem vacuum_coefficient_square (n : ℕ) (g : SchrodingerAction.CM.RealMp n) :
    ((SchrodingerAction.CM.action n g (Constructed.Vacuum.CM.vacuum (Fin n))).val 0) ^ 2 =
      (((RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).act (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)).position.det)⁻¹ := by
  obtain ⟨c, hc, hf⟩ := transformed_vacuum_amplitude n g
  rw [hf 0, RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian_zero, mul_one]
  have hn := ((RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).act (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)).position_det_ne_zero
  apply (mul_right_cancel₀ hn)
  rw [hc, inv_mul_cancel₀ hn]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CoverNormalization.CM.VacuumGraph

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CoverNormalization.CM

/-! The standard-frame position determinant is exactly PoissonAutomorphy's
momentum-position denominator. This verifies the remaining real
normalization clause for the constructed cover and vacuum. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum.CM

theorem transformed_position {n : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℝ) :
    ((RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).act g).position =
      (g.val.map Complex.ofRealHom).toBlocks₁₁ +
        (g.val.map Complex.ofRealHom).toBlocks₁₂ * (Complex.I • 1) := by
  have h := Matrix.fromBlocks_mul_fromRows
    (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1)
    (g.val.map Complex.ofRealHom).toBlocks₁₁
    (g.val.map Complex.ofRealHom).toBlocks₁₂
    (g.val.map Complex.ofRealHom).toBlocks₂₁
    (g.val.map Complex.ofRealHom).toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks, Matrix.mul_one] at h
  exact congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ => M.submatrix Sum.inl id) h

theorem swapped_blocks {n : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℝ) :
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g).val =
      Matrix.fromBlocks g.val.toBlocks₂₂ g.val.toBlocks₂₁ g.val.toBlocks₁₂ g.val.toBlocks₁₁ := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap = _
  nth_rw 1 [← Matrix.fromBlocks_toBlocks g.val]
  exact RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap_conjugation _ _ _ _

theorem base_denominator {n : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℝ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g)).complexify.denominator (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod (Fin n)).val =
      (g.val.map Complex.ofRealHom).toBlocks₁₂ * (Complex.I • 1) +
        (g.val.map Complex.ofRealHom).toBlocks₁₁ := by
  change ((RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g).val.toBlocks₂₁.map (algebraMap ℝ ℂ)) *
      Matrix.diagonal (fun _ => Complex.I) +
        ((RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g).val.toBlocks₂₂.map (algebraMap ℝ ℂ)) = _
  rw [swapped_blocks]
  simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  congr 1
  · congr 1
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]

theorem position_eq_denominator {n : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℝ) :
    ((RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).act g).position =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g)).complexify.denominator (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod (Fin n)).val := by
  rw [transformed_position, base_denominator, add_comm]

theorem real_normalization (n : ℕ) (g : SchrodingerAction.CM.RealMp n) :
    (((Constructed.RealCover.CM.realCover n).action g (Constructed.Vacuum.CM.vacuum (Fin n))).val 0) ^ 2 =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks ((Constructed.RealCover.CM.realCover n).project g)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod (Fin n)))⁻¹ := by
  have h := VacuumGraph.vacuum_coefficient_square n g
  rw [position_eq_denominator] at h
  exact h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CoverNormalization.CM

end

end OAI
