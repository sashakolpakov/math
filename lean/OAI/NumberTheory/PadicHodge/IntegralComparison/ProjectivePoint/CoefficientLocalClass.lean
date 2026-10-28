import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalTransferRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates

/-! # Coefficient Local Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CoefficientLocalClass

noncomputable section

/-! The original supported fixed point followed by the original
right map and inverse left map for an actual coefficient sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalTransferRecovery
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
variable {X : Scheme.{u}}
  (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2≤B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (v : M ⟶ Survivor.coefficient i s₀)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  {c g : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  (hcg : c+g=n+1)

def value :
    (PrincipalReference.Concentration.Reference.functor U hU (PrincipalPoint.Fraction.family U t)
      (c+g)).obj (GlobalTransferRecovery.coefficientDual B M) := by
  letI (q : ℕ) : ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB q
  letI (q : ℕ) : ((GlobalTransferRecovery.commonDual i s₀ B M v).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i s₀)
      (Survivor.chart (R := R)) B (n+2) hB v q
  letI := ProjectiveRefinement.DualMap.left_quasiIso M (Survivor.coefficient i s₀)
    (Survivor.chart (R := R)) B (n+2) hB v
  exact Principal.RelativeTransfer.map U hU (PrincipalPoint.Fraction.family U t) (c+g)
    (GlobalTransferRecovery.left i s₀ B M v) (GlobalTransferRecovery.right i s₀ B M v)
    (LocalCoordinates.pointAt i s₀ hbase B hB U hU s t hst hcg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CoefficientLocalClass
