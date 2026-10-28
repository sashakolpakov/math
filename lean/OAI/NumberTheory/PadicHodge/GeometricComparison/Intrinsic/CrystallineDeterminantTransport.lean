import OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsPullbackAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FrobeniusAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo

/-! # Crystalline Determinant Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.CrystallineDeterminantTransport

noncomputable section

/-! Determinants of the original crystalline pullbacks commute with
the actual split coefficient-field identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace SemilinearCharpoly

universe u v w z

variable {R : Type u} [Field R] {S : Type v} [Field S] (σ : R ≃+* S)
  {V : Type w} [AddCommGroup V] [Module R V]
  {W : Type z} [AddCommGroup W] [Module S W]

theorem native_det_map [FiniteDimensional R V] [FiniteDimensional S W]
    (e : V ≃ₛₗ[σ.toRingHom] W) (T : Module.End R V) (U : Module.End S W)
    (h : ∀ x, e (T x) = U (e x)) : U.det = σ T.det := by
  classical
  let b := Module.finBasis R V
  rw [← LinearMap.det_toMatrix (SemilinearCharpolyTo.SemilinearCharpoly.basis σ b e), ← LinearMap.det_toMatrix b,
    SemilinearCharpolyTo.SemilinearCharpoly.toMatrix_map σ b e T U h]
  exact (σ.map_det _).symm

end SemilinearCharpoly

namespace CrystallineAdapter

variable (q : ℕ) [Fact q.Prime]
  {X Y : Over (Spec (CommRingCat.of (ZMod q)))}
  [IsSeparated X.hom] [IsSeparated Y.hom]

theorem nativeSmallToBigEquiv_pullback (f : X ⟶ Y)
    (x : IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) Y 1) :
    Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv q X (PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q) f 1 x) =
      Crystalline.CoefficientAdapter.rationalPullback q f (Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv q Y x) := by
  obtain ⟨y, rfl⟩ := (PeriodInvariantsPullbackAdapter.CrystallineAdapter.nativeBigSmallEquiv q Y).surjective x
  rw [PeriodInvariantsPullbackAdapter.CrystallineAdapter.nativeBigSmallEquiv_pullback]
  change Crystalline.CoefficientAdapter.coefficientTensorEquiv q (Crystalline.CoefficientAdapter.IntegralH1 q X)
      ((PeriodInvariantsPullbackAdapter.CrystallineAdapter.nativeBigSmallEquiv q X).symm (PeriodInvariantsPullbackAdapter.CrystallineAdapter.nativeBigSmallEquiv q X (Crystalline.OperatorAdapter.CrystallineAdapter.fractionPullback q f y))) =
    Crystalline.CoefficientAdapter.rationalPullback q f
      (Crystalline.CoefficientAdapter.coefficientTensorEquiv q (Crystalline.CoefficientAdapter.IntegralH1 q Y)
        ((PeriodInvariantsPullbackAdapter.CrystallineAdapter.nativeBigSmallEquiv q Y).symm (PeriodInvariantsPullbackAdapter.CrystallineAdapter.nativeBigSmallEquiv q Y y)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact Crystalline.OperatorAdapter.CrystallineAdapter.coefficientEquiv_pullback q f y

omit Y in
theorem nativeSmall_finite_of_big
    [FiniteDimensional ℚ_[q] (Crystalline.CoefficientAdapter.RationalH1 q X)] :
    FiniteDimensional (FractionRing (Crystalline.CoefficientAdapter.Witt q))
      (IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) X 1) :=
  SemilinearCharpolyTo.SemilinearCharpoly.finite (Crystalline.CoefficientAdapter.coefficientFieldEquiv q).symm
    (Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv q X).symm

omit Y in
theorem nativeSmallToBigEquiv_det (f : X ⟶ X)
    [FiniteDimensional (FractionRing (Crystalline.CoefficientAdapter.Witt q))
      (IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) X 1)]
    [FiniteDimensional ℚ_[q] (Crystalline.CoefficientAdapter.RationalH1 q X)] :
    (Crystalline.CoefficientAdapter.rationalPullback q f).det = Crystalline.CoefficientAdapter.coefficientFieldEquiv q
      (PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q) f 1).det :=
  SemilinearCharpoly.native_det_map (Crystalline.CoefficientAdapter.coefficientFieldEquiv q)
    (Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv q X) _ _ (nativeSmallToBigEquiv_pullback q f)

end CrystallineAdapter

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.CrystallineDeterminantTransport
