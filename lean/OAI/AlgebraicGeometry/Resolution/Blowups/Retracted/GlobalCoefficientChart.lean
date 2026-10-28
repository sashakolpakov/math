import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientStep

/-! # Global Coefficient Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.GlobalCoefficientChart.Construction

noncomputable section

/-! A retained global coefficient chart with an actual algebraic line retraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Polynomial

structure GlobalCoefficientFamilyRetraction
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} (T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b) where
  base : CommRingCat
  algebra : Algebra ℂ base
  action : Algebra base T.ring
  lineAction : Algebra (Polynomial base) T.ring
  groundTower : IsScalarTower ℂ base T.ring
  lineTower : IsScalarTower base (Polynomial base) T.ring
  lineEtale : Algebra.Etale (Polynomial base) T.ring
  normal_eq : T.normal = algebraMap (Polynomial base) T.ring Polynomial.X
  derivative_eq : T.derivative = CoefficientStep.Construction.etaleLineOriginalNormalDerivation ℂ (H := base) (R := T.ring)
  retraction : (T.ring ⧸ Ideal.span {T.normal}) ≃ₐ[base] base

attribute [instance] GlobalCoefficientFamilyRetraction.algebra GlobalCoefficientFamilyRetraction.action
  GlobalCoefficientFamilyRetraction.lineAction GlobalCoefficientFamilyRetraction.groundTower
  GlobalCoefficientFamilyRetraction.lineTower GlobalCoefficientFamilyRetraction.lineEtale

theorem GlobalCoefficientFamilyRetraction.derivative_coefficient
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b}
    (A : GlobalCoefficientFamilyRetraction T) (c : A.base) :
    T.derivative (algebraMap A.base T.ring c) = 0 := by
  rw [A.derivative_eq]
  exact Derivation.map_algebraMap (HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := A.base) (V := T.ring)) c

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.GlobalCoefficientChart.Construction
