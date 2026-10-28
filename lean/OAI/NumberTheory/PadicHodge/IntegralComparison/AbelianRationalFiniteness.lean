import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianFiniteCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.Finiteness
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ScalarExtension
import OAI.NumberTheory.PadicHodge.GeometricComparison.Completion
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius

/-! # Abelian Rational Finiteness -/

namespace OAI.NumberTheory.PadicHodge

noncomputable section

/-! Finite generation and finite dimensionality of the actual integral and
rational pro-étale H¹ of an abelian variety, including the geometric special
fibre used by GeometricComparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.Obj

section

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

include hℓ

theorem IntegralComparison.AbelianRationalFiniteness.integral_finite : Module.Finite ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := by
  let : Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ 1 A.left).H 1) :=
    IntegralComparison.AbelianFiniteCoefficient.finite ℓ 1 A hℓ
  exact IntegralComparison.Integral.Finiteness.finite_of_finite_reduction ℓ A.left

theorem IntegralComparison.AbelianRationalFiniteness.rational_finite :
    FiniteDimensional ℚ_[ℓ] (IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ A.left 1) := by
  let : Module.Finite ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := IntegralComparison.AbelianRationalFiniteness.integral_finite ℓ A hℓ
  let : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  exact Module.Finite.of_surjective
    (GeometricComparison.Rational.ScalarExtension.RationalProEtaleCoefficients.rationalH1Equiv ℓ A.left).toLinearMap
    (GeometricComparison.Rational.ScalarExtension.RationalProEtaleCoefficients.rationalH1Equiv ℓ A.left).surjective

end

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

theorem GeometricComparison.Geometry.AbelianH1Model.native_etale_finite (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    FiniteDimensional ℚ_[ℓ] (A.Etale ℓ) := by
  let : GeometricallyIntegral A.specialFiber.scheme.hom := A.specialFiber_geometricallyIntegral
  let B := AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver (ZMod q) A.specialFiber.scheme
  let : IsProper B.hom := inferInstanceAs
    (IsProper (pullback.snd A.specialFiber.scheme.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))
  let : Smooth B.hom := inferInstanceAs
    (Smooth (pullback.snd A.specialFiber.scheme.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))
  let : GeometricallyIntegral B.hom := inferInstanceAs
    (GeometricallyIntegral
      (pullback.snd A.specialFiber.scheme.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))
  have hℓ : (ℓ : ZMod q) ≠ 0 := by
    intro hzero
    exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : ℓ.Prime)).mp
      ((ZMod.natCast_eq_zero_iff ℓ q).mp hzero)).symm
  have hℓ' : (ℓ : AlgebraicClosure (ZMod q)) ≠ 0 := by
    intro hzero
    apply hℓ
    apply (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective
    simpa only [map_natCast, map_zero] using hzero
  exact IntegralComparison.AbelianRationalFiniteness.rational_finite ℓ B hℓ'

end

end OAI.NumberTheory.PadicHodge
