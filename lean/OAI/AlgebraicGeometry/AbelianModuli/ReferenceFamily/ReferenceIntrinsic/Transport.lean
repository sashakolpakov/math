import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.HodgeKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse

/-! # Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Transport between the actual native period lattices of two reference
fibers. The arithmetic action on the prescribed subspaces proves the
Hodge condition for this concrete rational map. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z w : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {G : Reference.Fiber.ReferenceAnalyticFiber P w}
    {hP : P.IsAdmissible} (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (W : Reference.AlgebraicModel.ReferenceAlgebraicModel G hP)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods W.abelian :=
  M.nativeReferenceMarking.symm.trans ((g.restrictScalars ℚ).trans W.nativeReferenceMarking)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_marking (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.nativeReferenceTransport W g (M.nativeReferenceMarking v) = W.nativeReferenceMarking (g v) := by
  simp only [Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.restrictScalars_apply]

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_complex (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    (M.nativeReferenceTransport W g).toLinearMap.baseChange ℂ (M.nativeComplexReferenceMarking u) =
      W.nativeComplexReferenceMarking ((g.restrictScalars ℚ).toLinearMap.baseChange ℂ u) := by
  let L := ((M.nativeReferenceTransport W g).toLinearMap.baseChange ℂ).comp
    M.nativeComplexReferenceMarking.toLinearMap
  let R := W.nativeComplexReferenceMarking.toLinearMap.comp ((g.restrictScalars ℚ).toLinearMap.baseChange ℂ)
  change L u = R u
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)
  | tmul c v =>
    change c ⊗ₜ[ℚ] (M.nativeReferenceTransport W g (M.nativeReferenceMarking v)) =
      c ⊗ₜ[ℚ] W.nativeReferenceMarking (g v)
    rw [M.nativeReferenceTransport_marking]

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_integral (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hΛ : ∀ v, v ∈ P.lattice ↔ g v ∈ P.lattice) (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods M.abelian ↔ M.nativeReferenceTransport W g v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods W.abelian := by
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective v
  rw [M.nativeReferenceTransport_marking, M.nativeReferenceMarking_integral,
    W.nativeReferenceMarking_integral]
  exact hΛ v

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_hodge (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) (hw : w.val = P.lineAction g z.val) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure M.abelian) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure W.abelian)
      (M.nativeReferenceTransport W g).toLinearMap := by
  intro x hx
  obtain ⟨u, rfl⟩ := M.nativeComplexReferenceMarking.surjective x
  change (M.nativeReferenceTransport W g).toLinearMap.baseChange ℂ (M.nativeComplexReferenceMarking u) ∈
    (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection W.abelian).ker
  rw [M.nativeReferenceTransport_complex, W.nativeReferenceKernel, P.referenceComplexCoordinates_action, hw]
  exact P.referenceAmbientAction_period_mem hP g hg z.val z.property _ ((M.nativeReferenceKernel u).mp hx)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_inverse_hodge (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) (hw : w.val = P.lineAction g z.val) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure W.abelian) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure M.abelian)
      (M.nativeReferenceTransport W g).symm.toLinearMap :=
  HodgeInverse.isHodgeMap_inverse _ _ _ (M.nativeReferenceTransport_hodge W g hg hw)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
