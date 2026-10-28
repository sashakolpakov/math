import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernPairing
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicPolarization

/-! # Positive Periods -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Realize each positive period by an actual abelian variety and ample
algebraic line bundle whose original marked Chern form is the specified
integer matrix. All comparisons are constructed. Pending Lean validation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g}

theorem PositivePeriods.Geometric.integralLatticeForm_basis (T : DefinitionsIntegral.MarkedPolarizedTorus g E) (i j : DefinitionsIntegral.Index g) :
    DefinitionsIntegral.Geometric.integralLatticeForm T (DefinitionsIntegral.Geometric.integralLatticeBasis T i) (DefinitionsIntegral.Geometric.integralLatticeBasis T j) = E i j := by
  have h (k : DefinitionsIntegral.Index g) : (DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm (DefinitionsIntegral.Geometric.integralLatticeBasis T k) = Pi.single k 1 :=
    by
      simpa only [DefinitionsIntegral.Geometric.integralLatticeBasis, Module.Basis.map_apply, Pi.basisFun_apply] using
        (DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm_apply_apply ((Pi.basisFun ℤ (DefinitionsIntegral.Index g)) k)
  change Matrix.toBilin' E ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm (DefinitionsIntegral.Geometric.integralLatticeBasis T i))
    ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm (DefinitionsIntegral.Geometric.integralLatticeBasis T j)) = E i j
  rw [h i, h j]
  exact Matrix.toBilin'_single E i j

section
variable {T : DefinitionsIntegral.MarkedPolarizedTorus g E} (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

def PeriodModel.Geometric.AlgebraicPeriodModel.markedNativeBasis : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) M.abelian :=
  (DefinitionsIntegral.Geometric.integralLatticeBasis T).map M.nativeLatticeEquiv

theorem PeriodModel.Geometric.AlgebraicPeriodModel.markedNativeBasis_periodMap :
    ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap M.markedNativeBasis = M.periodDifferential.toLinearMap.comp T.periodMap := by
  apply (Pi.basisFun ℂ (DefinitionsIntegral.Index g)).ext
  intro i
  rw [ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap, Module.Basis.constr_basis]
  change M.periodDifferential
    (T.periodMap (fun j => (((Pi.basisFun ℤ (DefinitionsIntegral.Index g)) i) j : ℂ))) =
      M.periodDifferential (T.periodMap ((Pi.basisFun ℂ (DefinitionsIntegral.Index g)) i))
  rw [DefinitionsIntegral.integralInclusion_basis]

theorem PeriodModel.Geometric.AlgebraicPeriodModel.markedNativeBasis_kernel : (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap M.markedNativeBasis).ker = T.periodMap.ker := by
  rw [M.markedNativeBasis_periodMap]
  ext v
  change M.periodDifferential (T.periodMap v) = 0 ↔ T.periodMap v = 0
  exact map_eq_zero_iff M.periodDifferential M.periodDifferential.injective

theorem PeriodModel.Geometric.AlgebraicPeriodModel.markedNativeBasis_polarization
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left) (hL : L.IsAmple)
    (hpair : ∀ l m : T.lattice, AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L
      (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ)) :
    IntrinsicPolarization.Geometric.PreservesPolarizationMatrix M.abelian L hL M.markedNativeBasis E := by
  intro i j
  have h := AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_period M.abelian L hL
    (M.nativeIntegralPeriod (DefinitionsIntegral.Geometric.integralLatticeBasis T i))
    (M.nativeIntegralPeriod (DefinitionsIntegral.Geometric.integralLatticeBasis T j))
  rw [hpair, PositivePeriods.Geometric.integralLatticeForm_basis] at h
  change (AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm M.abelian L hL
    (M.periodDifferential (DefinitionsIntegral.Geometric.integralLatticeBasis T i).val)
    (M.periodDifferential (DefinitionsIntegral.Geometric.integralLatticeBasis T j).val)).im = (E i j : ℝ)
  change (AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm M.abelian L hL
    (M.periodDifferential (DefinitionsIntegral.Geometric.integralLatticeBasis T i).val)
    (M.periodDifferential (DefinitionsIntegral.Geometric.integralLatticeBasis T j).val)).im = ((E i j : ℚ) : ℝ) at h
  simpa only [Rat.cast_intCast] using h

end

/-- Actual algebraic realization with the specified original polarization. -/
theorem PositivePeriods.Geometric.algebraic_positive_period_realization
    (E : DefinitionsIntegral.IntegralMatrix g) (hE : E.transpose = -E)
    (P : Submodule ℂ (DefinitionsIntegral.CVec g)) (hP : DefinitionsIntegral.CompatiblePositivePeriod E P) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
      (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A),
      IntrinsicPolarization.Geometric.PreservesPolarizationMatrix A L hL b E ∧ (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker = P := by
  obtain ⟨T, hT⟩ := DefinitionsIntegral.realize_positive_period E hE P hP
  obtain ⟨M⟩ := PeriodModel.Geometric.exists_algebraicPeriodModel T
  obtain ⟨L, hL, hpair⟩ := M.exists_ample_native_chern_pairing (hP := hE)
  exact ⟨M.abelian, L, hL, M.markedNativeBasis,
    M.markedNativeBasis_polarization L hL hpair, M.markedNativeBasis_kernel.trans hT⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
