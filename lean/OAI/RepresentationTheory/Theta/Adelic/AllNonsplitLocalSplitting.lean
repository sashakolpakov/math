import OAI.RepresentationTheory.Theta.Adelic.RealFieldLocalSplitting
import OAI.RepresentationTheory.Theta.Adelic.NonsplitLocalSplitting

/-! # All Nonsplit Local Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.AllNonsplitLocalSplitting

noncomputable section

/-! The actual normalized local splitting at every nonsplit local field,
combining the ultrametric and real constructions. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k]

theorem all_nonsplit_local_splitting
    (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k) {n m : ℕ}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H.val K.val)
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)
    (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle)
    (hV : ∀ a : kˣ, χV (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ n)
    (hW : ∀ a : kˣ, χW (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ m)
    (bH bK : kˣ)
    (hbH : QuadraticNormSquareQuotient.scalarUnits d bH = Matrix.GeneralLinearGroup.det H)
    (hbK : QuadraticNormSquareQuotient.scalarUnits d bK = (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s (g, 1)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
          ((Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bK : ℂ) ^ n *
            (χW ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ)) *
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (g, 1)) f.val h.val) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s (1, g)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
          ((Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d bH : ℂ) ^ m *
            (χV (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ)) *
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (1, g)) f.val h.val) := by
  by_cases hArch : ∀ j : ℕ, ‖(j : k)‖ ≤ 1
  · let : IsUltrametricDist k := IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    exact NonsplitLocalSplitting.nonsplit_local_splitting d hd hns hnd H K hH hK P
      ψ hc hu hn χV χW hV hW bH bK hbH hbK
  · rcases Weil.Local.ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, hi⟩ | ⟨e, _, _⟩
    · exact RealFieldLocalSplitting.real_field_local_splitting d hd hns hnd hArch e he hi
        H K hH hK P ψ hc hu hn χV χW hV hW bH bK hbH hbK
    · exfalso
      apply hns
      refine ⟨e.symm ((e d) ^ (1 / 2 : ℂ)), e.injective ?_⟩
      rw [map_mul, e.apply_symm_apply, ← pow_two]
      simp [one_div]

end

end OAI.RepresentationTheory.Theta.Adelic.AllNonsplitLocalSplitting
