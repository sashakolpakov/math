import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChartKernelIdeal
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SingleProjectiveChart
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PolynomialKernel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient

/-! # Intrinsic Coordinate Ideal -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicCoordinateIdeal

noncomputable section

/-! The saturated homogeneous coordinate ideal obtained from the actual
closed ideal on projective charts. Its degree-m part is exactly the kernel
of the actual polynomial restriction map to the native O(m) pullback. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

def nativeProjectiveDehomogenize (i : σ) :
    MvPolynomial σ Γ(Spec (.of R), ⊤) →+*
      Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
  (SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i).symm.toRingHom.comp
    (SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤) (fun _ : Fin 1 => i))

omit [LinearOrder σ] in
theorem nativeProjectiveDehomogenize_self (i : σ) :
    nativeProjectiveDehomogenize (R := R) i (MvPolynomial.X i) = 1 := by
  classical
  have h : SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartExponent (fun _ : Fin 1 => i)
      (Finsupp.single i 1) = 0 := by
    apply Subtype.ext
    ext q
    simp [SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartExponent, Finsupp.single_eq_of_ne q.property]
  change (SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i).symm
    (SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤) (fun _ : Fin 1 => i)
      (MvPolynomial.monomial (Finsupp.single i 1) 1)) = 1
  rw [SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, h]
  exact map_one _

theorem nativeProjectiveDehomogenize_section (i j : σ) (m : ℕ)
    (x : Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤)) :
    nativeProjectiveDehomogenize i
      (SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m x).val =
      SheafCohomology.Projective.FrameSections.localTrivializationCoefficient _
        ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j m) x := by
  let a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 :=
    ⟨fun _ => ⟨i⟩, Subsingleton.strictMono (α := Fin 1) _⟩
  have h := SheafCohomology.Projective.PolynomialChartFrameCoefficient.MvPolynomial.coordinateTwistPolynomial_chartCoefficientRingHom j m x a
  rw [SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame,
    SheafCohomology.Projective.PositivePowerChartGenerator.overCoefficient_eq_localCoefficient _
      ⟨_, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩] at h
  apply (SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i).injective
  change (SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i)
    ((SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i).symm _) = _
  rw [RingEquiv.apply_symm_apply, SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv_apply]
  exact h

variable {X : Scheme.{u}} (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [QuasiCompact f]

def nativeProjectiveCoordinateIdeal :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤)) :=
  ChartKernelIdeal.PolarizationEmbedding.chartKernelIdeal (nativeProjectiveDehomogenize (R := R))
    (fun i => f.ker.ideal ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i,
      SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩)

omit [LinearOrder σ] [QuasiCompact f] in
theorem nativeProjectiveCoordinateIdeal_saturated
    (p : MvPolynomial σ Γ(Spec (.of R), ⊤)) (d : ℕ) (hp : p.IsHomogeneous d)
    (h : ∃ m : ℕ, ∀ q : MvPolynomial σ Γ(Spec (.of R), ⊤), q.IsHomogeneous m →
      q * p ∈ (nativeProjectiveCoordinateIdeal f).toIdeal) :
    p ∈ (nativeProjectiveCoordinateIdeal f).toIdeal :=
  ChartKernelIdeal.PolarizationEmbedding.chartKernelIdeal_saturated _ _
    (fun i => by rw [nativeProjectiveDehomogenize_self]; exact isUnit_one) p d hp h

theorem nativePolynomialRestriction_zero_iff_mem_coordinateIdeal (j : σ) (m : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤) m) :
    Projective.PolynomialRestriction.PolarizationEmbedding.nativePolynomialRestriction f j m p = 0 ↔
      p.val ∈ (nativeProjectiveCoordinateIdeal f).toIdeal := by
  rw [Projective.PolynomialKernel.PolarizationEmbedding.nativePolynomialRestriction_zero_iff, nativeProjectiveCoordinateIdeal,
    ChartKernelIdeal.PolarizationEmbedding.mem_chartKernelIdeal _ _ p.property]
  apply forall_congr'
  intro i
  rw [← nativeProjectiveDehomogenize_section i j m,
    LinearEquiv.apply_symm_apply]

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicCoordinateIdeal
