import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestRationalMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Test Lattice -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The constructed native reference marking identifies the entire
original integral lattice with the actual test fiber's integral periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referenceTestFiberIso Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.nativeReferenceTestRationalMarking_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy v ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety ↔
        v ∈ P.lattice := by
  let e := M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy
  let R := Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP
  have : IsMonHom e.hom := M.nativeReferenceTestFiberIso_group hM κ hP hκ f a y hy
  change Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom (R.nativeReferenceMarking v) ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods _ ↔ _
  exact (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso_integral_iff e (R.nativeReferenceMarking v)).trans
    (R.nativeReferenceMarking_integral v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
