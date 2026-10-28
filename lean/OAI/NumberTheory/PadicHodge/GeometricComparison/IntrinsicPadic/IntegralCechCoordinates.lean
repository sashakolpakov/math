import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover

/-! # Integral Cech Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates

noncomputable section

/-! Native de Rham H-one and its completion coordinates on the actual
integral etale coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

def equiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 ≃ₗ[ℤ_[p]] (C).homology 1 :=
  (Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv ℤ_[p] X U
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)).symm.trans
      (((C).extendHomologyIso ComplexShape.embeddingUpNat (j := 1) rfl).toLinearEquiv)

local instance padic_complete : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

def completion : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 ≃ₗ[ℤ_[p]]
    IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.compatible ℤ_[p] X U (p : ℤ_[p]) 1 :=
  IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.nativeHoneEquiv ℤ_[p] X U
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)
    (p : ℤ_[p]) (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

theorem completion_eval (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) (n : ℕ) :
    (completion p X x).val n = CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] C (p : ℤ_[p]) n 1 (equiv p X x) :=
  IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.equiv_eval ℤ_[p] X U
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)
    (p : ℤ_[p]) (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    1 le_rfl (equiv p X x) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates
