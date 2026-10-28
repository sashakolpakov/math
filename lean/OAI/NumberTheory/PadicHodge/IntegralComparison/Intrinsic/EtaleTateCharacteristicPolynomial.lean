import OAI.NumberTheory.PadicHodge.IntegralComparison.TateCharacteristicPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianRationalFiniteness
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding

/-! # Etale Tate Characteristic Polynomial -/

namespace OAI.NumberTheory.PadicHodge

noncomputable section

/-! The original rational pro-étale Frobenius used by GeometricComparison has exactly
the characteristic polynomial of the actual geometric Tate Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

abbrev GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber := AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver (ZMod q) A.specialFiber.scheme

local instance GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_group : GrpObj A.geometricSpecialFiber :=
  inferInstanceAs (GrpObj (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver (ZMod q) A.specialFiber.scheme))

local instance GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_commutative : IsCommMonObj A.geometricSpecialFiber :=
  inferInstanceAs (IsCommMonObj (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver (ZMod q) A.specialFiber.scheme))

local instance GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_proper : IsProper A.geometricSpecialFiber.hom :=
  inferInstanceAs (IsProper
    (Limits.pullback.snd A.specialFiber.scheme.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))

local instance GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_smooth : Smooth A.geometricSpecialFiber.hom :=
  inferInstanceAs (Smooth
    (Limits.pullback.snd A.specialFiber.scheme.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))

local instance GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_integral : GeometricallyIntegral A.geometricSpecialFiber.hom := by
  let : GeometricallyIntegral A.specialFiber.scheme.hom := A.specialFiber_geometricallyIntegral
  exact inferInstanceAs (GeometricallyIntegral
    (Limits.pullback.snd A.specialFiber.scheme.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))

theorem GeometricComparison.Geometry.AbelianH1Model.ell_ne_zero_in_geometricField (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    (ℓ : AlgebraicClosure (ZMod q)) ≠ 0 := by
  have hℓ : (ℓ : ZMod q) ≠ 0 := by
    intro hzero
    exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : ℓ.Prime)).mp
      ((ZMod.natCast_eq_zero_iff ℓ q).mp hzero)).symm
  intro hz
  apply hℓ
  apply (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective
  simpa only [map_natCast, map_zero] using hz

abbrev GeometricComparison.Geometry.AbelianH1Model.NativeTate (ℓ : ℕ) [Fact ℓ.Prime] := AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := IntegralComparison.Geometric.TateModule.Points A.geometricSpecialFiber) ℓ

def GeometricComparison.Geometry.AbelianH1Model.nativeTateFrobenius (ℓ : ℕ) [Fact ℓ.Prime] : Module.End ℤ_[ℓ] (A.NativeTate ℓ) :=
  IntegralComparison.Integral.TateNaturality.tateAction ℓ A.geometricSpecialFiber
    (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange (ZMod q) A.specialFiber.scheme
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme))

theorem GeometricComparison.Geometry.AbelianH1Model.native_tate_finite (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    Module.Finite ℤ_[ℓ] (A.NativeTate ℓ) :=
  IntegralComparison.Geometric.TateModule.finite A.geometricSpecialFiber ℓ (GeometricComparison.Geometry.AbelianH1Model.ell_ne_zero_in_geometricField ℓ hℓq)

theorem GeometricComparison.Geometry.AbelianH1Model.native_tate_free (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    Module.Free ℤ_[ℓ] (A.NativeTate ℓ) :=
  IntegralComparison.Geometric.TateModule.free A.geometricSpecialFiber ℓ (GeometricComparison.Geometry.AbelianH1Model.ell_ne_zero_in_geometricField ℓ hℓq)

theorem GeometricComparison.Geometry.AbelianH1Model.native_geometric_finite (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    FiniteDimensional (AlgebraicClosure ℚ_[ℓ]) (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.GeometricH1 ℓ A.specialFiber.scheme) := by
  let B := A.geometricSpecialFiber
  let : Module.Finite ℤ_[ℓ] (B.left.EllAdicCohomology ℓ 1) :=
    IntegralComparison.TateCharacteristicPolynomial.integral_finite ℓ B
      (GeometricComparison.Geometry.AbelianH1Model.ell_ne_zero_in_geometricField ℓ hℓq)
  exact inferInstanceAs (Module.Finite (AlgebraicClosure ℚ_[ℓ])
    ((AlgebraicClosure ℚ_[ℓ]) ⊗[ℤ_[ℓ]] B.left.EllAdicCohomology ℓ 1))

theorem GeometricComparison.Geometry.AbelianH1Model.native_geometric_charpoly_eq_tate (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI := A.native_geometric_finite ℓ hℓq
    letI := A.native_tate_finite ℓ hℓq
    letI := A.native_tate_free ℓ hℓq
    (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ (ZMod q) A.specialFiber.scheme).charpoly =
      (A.nativeTateFrobenius ℓ).charpoly.map
        (algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) := by
  let B := A.geometricSpecialFiber
  let hℓ := GeometricComparison.Geometry.AbelianH1Model.ell_ne_zero_in_geometricField ℓ hℓq
  let e := AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange (ZMod q) A.specialFiber.scheme
    (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme)
  let : Module.Finite ℤ_[ℓ] (A.NativeTate ℓ) := A.native_tate_finite ℓ hℓq
  let : Module.Free ℤ_[ℓ] (A.NativeTate ℓ) := A.native_tate_free ℓ hℓq
  let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := IntegralComparison.Geometric.TateModule.Points B) ℓ) := IntegralComparison.Geometric.TateModule.finite B ℓ hℓ
  let : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := IntegralComparison.Geometric.TateModule.Points B) ℓ) := IntegralComparison.Geometric.TateModule.free B ℓ hℓ
  let : Module.Finite ℤ_[ℓ] (B.left.EllAdicCohomology ℓ 1) :=
    IntegralComparison.TateCharacteristicPolynomial.integral_finite ℓ B hℓ
  let : Module.Free ℤ_[ℓ] (B.left.EllAdicCohomology ℓ 1) :=
    IntegralComparison.TateCharacteristicPolynomial.integral_free ℓ B hℓ
  let : FiniteDimensional (AlgebraicClosure ℚ_[ℓ]) (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.GeometricH1 ℓ A.specialFiber.scheme) :=
    A.native_geometric_finite ℓ hℓq
  have he := IntegralComparison.TateCharacteristicPolynomial.integral_charpoly ℓ B hℓ e
  dsimp only at he
  change ((AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1).baseChange
    (AlgebraicClosure ℚ_[ℓ])).charpoly = _
  rw [LinearMap.charpoly_baseChange, he]
  rfl

theorem GeometricComparison.Geometry.AbelianH1Model.native_etale_charpoly_eq_tate (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI := A.native_etale_finite ℓ hℓq
    letI := A.native_tate_finite ℓ hℓq
    letI := A.native_tate_free ℓ hℓq
    (A.etaleFrobenius ℓ).toLinearMap.charpoly =
      (A.nativeTateFrobenius ℓ).charpoly.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
  let : Module.Finite ℤ_[ℓ] (A.NativeTate ℓ) := A.native_tate_finite ℓ hℓq
  let : Module.Free ℤ_[ℓ] (A.NativeTate ℓ) := A.native_tate_free ℓ hℓq
  let : FiniteDimensional ℚ_[ℓ] (A.Etale ℓ) := A.native_etale_finite ℓ hℓq
  let : FiniteDimensional (AlgebraicClosure ℚ_[ℓ]) (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.GeometricH1 ℓ A.specialFiber.scheme) :=
    A.native_geometric_finite ℓ hℓq
  let : FiniteDimensional (AlgebraicClosure ℚ_[ℓ])
      (GeometricComparison.AlgebraicRational.RationalProEtaleCoefficients.AlgebraicRationalH1 ℓ (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A.specialFiber.scheme)) :=
    inferInstanceAs (FiniteDimensional (AlgebraicClosure ℚ_[ℓ])
      ((AlgebraicClosure ℚ_[ℓ]) ⊗[ℚ_[ℓ]] A.Etale ℓ))
  have hcompare := IntegralComparison.DualCharacteristicPolynomial.of_intertwines
    (GeometricComparison.AlgebraicRational.RationalProEtaleCoefficients.algebraicH1Equiv ℓ (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A.specialFiber.scheme))
    (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ (ZMod q) A.specialFiber.scheme)
    ((A.etaleFrobenius ℓ).toLinearMap.baseChange (AlgebraicClosure ℚ_[ℓ]))
    (GeometricComparison.Rational.GeometricRationalComparison.geometricFrobenius_compare q A.specialFiber.scheme ℓ)
  apply Polynomial.map_injective _ (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).injective
  rw [← LinearMap.charpoly_baseChange, ← hcompare, A.native_geometric_charpoly_eq_tate ℓ hℓq, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq ℤ_[ℓ] ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])]

end

end OAI.NumberTheory.PadicHodge
