import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.Transport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality

/-! # Map Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! A genuine algebraic group map with specified reference period
values transports the prescribed period kernel by the same E-linear map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z w : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {G : Reference.Fiber.ReferenceAnalyticFiber P w}
    {hP : P.IsAdmissible} (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (W : Reference.AlgebraicModel.ReferenceAlgebraicModel G hP)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (f : M.abelian.toOver ⟶ W.abelian.toOver) [IsMonHom f]
    (hf : ∀ v, W.nativeReferenceMarking (g v) = Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (M.nativeReferenceMarking v))

include hf in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_eq_rationalLift : (M.nativeReferenceTransport W g).toLinearMap = Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f := by
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective v
  exact (M.nativeReferenceTransport_marking W g v).trans (hf v)

include hf in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.referenceAmbientAction_mem_of_native_map (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (hu : u ∈ P.periodFamily z.val) :
    P.referenceAmbientAction g u ∈ P.periodFamily w.val := by
  obtain ⟨v, rfl⟩ := (P.referenceComplexCoordinates hP).surjective u
  have h := PeriodProjectionNaturality.IntrinsicLinearMaps.rationalLift_isHodgeMap f (M.nativeComplexReferenceMarking v) ((M.nativeReferenceKernel v).mpr hu)
  change (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).baseChange ℂ (M.nativeComplexReferenceMarking v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection W.abelian).ker at h
  rw [← M.nativeReferenceTransport_eq_rationalLift W g f hf, M.nativeReferenceTransport_complex,
    W.nativeReferenceKernel, P.referenceComplexCoordinates_action] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
