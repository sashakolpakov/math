import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalTransferRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal

/-! # Canonical Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CanonicalTransfer

noncomputable section

/-! Canonical complementary affine covers discharge the refinement
condition for the original projective point transfer. Coverage is only
required on the actual closed subscheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry
  GlobalTransferRecovery
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} [X.IsSeparated]
  (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (v : M ⟶ Survivor.coefficient i s₀)
  (d : ℕ) (hM : ∀ q, q ≠ d → (GlobalTransferRecovery.coefficientDual B M).ExactAt q)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : (GlobalTransferRecovery.coefficientDual B M).homology d ≅ (Scheme.Modules.pushforward i).obj N)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  {c g : ℕ} (a : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (ha : Ideal.span (Set.range a) = i.ker.ideal ⟨U, hU⟩)
  (hat : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) a t =
    (s₀ ≫ i).ker.ideal ⟨U, hU⟩)

include hB ha hat hM N e in
omit [Module.Injective R R] in
theorem refinement_isIso : IsIso (RelativeCech.Refinement.homology
    (Principal.RelativeConcentration.ambient U hU) (PrincipalPoint.RelativeGeometry.complementary i s₀)
    (PrincipalPoint.RelativeGeometry.common i s₀ U hU t) (PrincipalPoint.RelativeGeometry.right i s₀ U hU t)
    (Relative.AdditiveCechConcentration.coefficients (GlobalTransferRecovery.coefficientDual B M)) (n+1)) := by
  let : ∀ q, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
  exact PrincipalPoint.RelativeGeometry.right_isIso i s₀ U hU a t ha
    ((KoszulPoint.Ideal.append _ a t).symm.trans hat)
    (GlobalTransferRecovery.coefficientDual B M) d hM N e (n+1)

abbrev localize_recovery := by
  letI := refinement_isIso i s₀ B hB M d hM N e U hU a t ha hat
  exact GlobalTransferRecovery.localize_recovery i s₀ hbase B hB M v
    U hU a t hat (PrincipalPoint.RelativeGeometry.complementary i s₀) (PrincipalPoint.RelativeGeometry.complementary_affine i s₀)
    (PrincipalPoint.RelativeGeometry.common i s₀ U hU t) (PrincipalPoint.RelativeGeometry.common_affine i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.left i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.right i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.complementary_outside i s₀) (PrincipalPoint.RelativeGeometry.common_outside i s₀ U hU t)

abbrev map_recovery := by
  letI := refinement_isIso i s₀ B hB M d hM N e U hU a t ha hat
  exact GlobalTransferRecovery.map_recovery i s₀ hbase B hB M v
    U hU a t hat (PrincipalPoint.RelativeGeometry.complementary i s₀) (PrincipalPoint.RelativeGeometry.complementary_affine i s₀)
    (PrincipalPoint.RelativeGeometry.common i s₀ U hU t) (PrincipalPoint.RelativeGeometry.common_affine i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.left i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.right i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.complementary_outside i s₀) (PrincipalPoint.RelativeGeometry.common_outside i s₀ U hU t)

variable [IsArtinianRing R] [IsLocalRing R]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev point_recovery := ConcreteCategory.congr_hom
  (map_recovery i s₀ hbase B hB M v d hM N e U hU a t ha hat)
    (SupportedClass.fixedPointClass i s₀ hbase B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CanonicalTransfer
