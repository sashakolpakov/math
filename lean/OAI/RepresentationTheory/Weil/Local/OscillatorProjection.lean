import OAI.RepresentationTheory.Weil.Local.GenerationSymplectic
import OAI.RepresentationTheory.Weil.Local.FourierEquivalence
import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner

/-! # Oscillator Projection -/

namespace OAI.RepresentationTheory.Weil.Local.OscillatorProjection.Construction

noncomputable section

/-! The oscillator projection and normality of the intrinsic bare subgroup. -/

open scoped commutatorElement

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ψ : AddChar k ℂ)

def oscillatorProjection : FunctionsMetaplectic.Construction.Oscillator k n ψ →* FunctionsMetaplectic.Construction.Symplectic k n :=
  (MonoidHom.fst _ _).comp (FunctionsMetaplectic.Construction.oscillatorSubgroup k n ψ).subtype

theorem oscillatorMinus_commute (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) :
    Commute (FunctionsMetaplectic.Construction.oscillatorMinus k n ψ) g := by
  change FunctionsMetaplectic.Construction.oscillatorMinus k n ψ * g = g * FunctionsMetaplectic.Construction.oscillatorMinus k n ψ
  apply Subtype.ext
  apply Prod.ext
  · change 1 * g.val.1 = g.val.1 * 1
    simp
  · apply LinearEquiv.ext
    intro f
    change -(g.val.2 f) = g.val.2 (-f)
    exact (g.val.2.map_neg f).symm

theorem oscillatorMinus_conjugation (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) :
    g * FunctionsMetaplectic.Construction.oscillatorMinus k n ψ * g⁻¹ = FunctionsMetaplectic.Construction.oscillatorMinus k n ψ := by
  rw [← (oscillatorMinus_commute k n ψ g).eq, mul_assoc, mul_inv_cancel, mul_one]

instance metaplecticSubgroup_normal : (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).Normal where
  conj_mem z hz g := by
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with hz | hz
        · obtain ⟨u, v, rfl⟩ := hz
          apply Subgroup.subset_closure
          left
          exact ⟨g * u * g⁻¹, g * v * g⁻¹, (conjugate_commutatorElement u v g).symm⟩
        · obtain rfl := hz
          rw [oscillatorMinus_conjugation]
          exact Subgroup.subset_closure (Or.inr rfl)
    | one => simp
    | mul a b _ _ ha hb =>
        rw [← conj_mul]
        exact (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).mul_mem ha hb
    | inv a _ ha =>
        rw [← conj_inv]
        exact (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).inv_mem ha

omit [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] in
theorem upper_quadratic_conjugation (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    GenerationSymplectic.Construction.upperSymplectic B = (Generators.Construction.weylSymplectic k n)⁻¹ *
      Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ * Generators.Construction.weylSymplectic k n := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 B.val 0 1 =
    ((Generators.Construction.weylSymplectic k n)⁻¹).val * (Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩).val *
      (Generators.Construction.weylSymplectic k n).val
  rw [SymplecticGroup.coe_inv]
  simp [Generators.Construction.weylSymplectic, Generators.Construction.quadraticSymplectic, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

theorem real_oscillatorProjection_surjective_standard :
    Function.Surjective (oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1)) := by
  apply MonoidHom.range_eq_top.mp
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_generators
  · intro B
    refine ⟨(FourierEquivalence.Construction.realFourierOscillator n)⁻¹ *
      QuadraticIntertwiner.Construction.realQuadraticOscillator 1 ⟨-B.val, B.property.neg⟩ * FourierEquivalence.Construction.realFourierOscillator n, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact (upper_quadratic_conjugation ℝ n B).symm
  · intro A
    exact ⟨LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter 1) A, rfl⟩
  · exact ⟨FourierEquivalence.Construction.realFourierOscillator n, rfl⟩

end

end OAI.RepresentationTheory.Weil.Local.OscillatorProjection.Construction
