import OAI.RepresentationTheory.Weil.Local.FrameGaussianAction
import OAI.RepresentationTheory.Weil.Local.GeneralSchur
import OAI.RepresentationTheory.Weil.Local.BareGeneration

/-! # Real Standard Bare Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction

noncomputable section

/-! The real intrinsic bare cover has only scalar signs for the standard character. -/

open _root_.Matrix _root_.MeasureTheory

theorem real_standard_character_nontrivial : ∃ t : ℝ, Gaussian.Construction.realCharacter 1 t ≠ 1 := by
  refine ⟨1 / 2, ?_⟩
  have he : Gaussian.Construction.realCharacter 1 (1 / 2) = -1 := by
    rw [Gaussian.Construction.realCharacter_apply]
    convert Complex.exp_pi_mul_I using 1
    congr 1
    push_cast
    ring
  rw [he]
  norm_num

theorem realGaussianSubgroup_projection (n : ℕ) :
    (FrameGaussianAction.Construction.realGaussianSubgroup n).map (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1)) = ⊤ := by
  let H := FrameGaussianAction.Construction.realGaussianSubgroup n
  obtain ⟨w, hwπ, hw⟩ := RealWeyl.Construction.exists_real_weyl_metaplectic_parameter n 1 one_ne_zero
  have hwH : w.val ∈ H := FrameGaussianAction.Construction.realGaussianSubgroup_weyl w hwπ hw
  have hwπ' : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) w.val = Generators.Construction.weylSymplectic ℝ n := hwπ
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 ⟨-B.val, B.property.neg⟩
    refine ⟨w.val⁻¹ * u.val * w.val,
      H.mul_mem (H.mul_mem (H.inv_mem hwH) (FrameGaussianAction.Construction.realGaussianSubgroup_lower _)) hwH, ?_⟩
    rw [map_mul, map_mul, map_inv, hwπ']
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℝ n B).symm
  · intro B
    exact ⟨(QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 B).val, FrameGaussianAction.Construction.realGaussianSubgroup_lower B, rfl⟩

theorem real_standard_metaplectic_le_gaussianSubgroup (n : ℕ) :
    FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter 1) ≤ FrameGaussianAction.Construction.realGaussianSubgroup n := by
  let H := FrameGaussianAction.Construction.realGaussianSubgroup n
  have hsurj := realGaussianSubgroup_projection n
  have hnd : ¬ DiscreteTopology ℝ := by
    intro h
    let : DiscreteTopology ℝ := h
    have : Subsingleton ℝ := subsingleton_of_preconnected_totallyDisconnected
    exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)
  have hder : commutator (FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter 1)) ≤ H :=
    BareGeneration.Construction.commutator_le_of_central_kernel (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1)) H
      (fun x => by
        have h : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) x ∈
            H.map (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1)) := by rw [hsurj]; trivial
        exact h)
      (fun z hz x => GeneralSchur.Construction.oscillator_kernel_central hnd (Gaussian.Construction.realCharacter 1)
        (RealTestSpace.Construction.realCharacter_temperate 1).1.continuous (QuadraticIntertwiner.Construction.realCharacter_unitary 1)
        real_standard_character_nontrivial z hz x)
  change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter 1)) ∪
    {FunctionsMetaplectic.Construction.oscillatorMinus ℝ n (Gaussian.Construction.realCharacter 1)}) ≤ H
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · apply hder
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure hx
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact FrameGaussianAction.Construction.realGaussianSubgroup_minus n

theorem real_standard_metaplectic_kernel_sign {n : ℕ}
    (a : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter 1))
    (ha : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter 1) a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, a.val.val.2 f = ε • f := by
  obtain ⟨z, _, hscalar⟩ := OscillatorSchur.Construction.real_oscillator_kernel_scalar (Gaussian.Construction.realCharacter 1)
    (RealTestSpace.Construction.realCharacter_temperate 1).1.continuous (QuadraticIntertwiner.Construction.realCharacter_unitary 1)
    real_standard_character_nontrivial a.val ha
  have hgraph := real_standard_metaplectic_le_gaussianSubgroup n a.property
  let P := SiegelGaussian.Construction.standardPositiveFrame n
  have hd : P.position.det = 1 := Matrix.det_one
  have hin : FrameGaussianAction.Construction.realGaussianGraph P P.gaussianLp := ⟨1, by rw [one_pow, one_mul, hd], by rw [one_smul]⟩
  have hout := (hgraph P P.gaussianLp).mp hin
  have hproj : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a.val = 1 := ha
  rw [hproj, P.act_one, RealOscillator.Construction.realL2Oscillator_scalar _ _ _ _ hscalar] at hout
  obtain ⟨ε, hε, hz⟩ := hout
  have he : z = ε := smul_left_injective ℂ P.gaussianLp_ne_zero hz
  refine ⟨z, ?_, hscalar⟩
  rw [he]
  simpa only [hd, mul_one] using hε

end

end OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction
