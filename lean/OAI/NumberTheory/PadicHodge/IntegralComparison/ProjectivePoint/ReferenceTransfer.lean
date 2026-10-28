import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CanonicalTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.NormalizedClassTransfer

/-! # Reference Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ReferenceTransfer.Reference

noncomputable section

/-! The actual localized fixed point class, after its original
common-resolution transfer and the canonical cover comparison, is the
original native projective total map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry
  GlobalTransferRecovery
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
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
  (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {c g : ℕ} (a : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (ha : Ideal.span (Set.range a) = i.ker.ideal ⟨U, hU⟩)
  (hat : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) a t =
    (s₀ ≫ i).ker.ideal ⟨U, hU⟩)
local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2))
local notation "V" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
local notation "haV" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) (σ := Fin (n+2))
local notation "hV" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2))

abbrev recovery := by
  letI : ∀ q, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
  letI : ∀ q, ((Survivor.dual i s₀ B).X q).IsQuasicoherent :=
    PrincipalConcentration.terms_qc i s₀ B hB
  letI : ∀ q, ((GlobalTransferRecovery.commonDual i s₀ B M v).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i s₀)
      (Survivor.chart (R := R)) B (n+2) hB v
  letI := ProjectiveRefinement.DualMap.left_quasiIso M (Survivor.coefficient i s₀)
    (Survivor.chart (R := R)) B (n+2) hB v
  letI := CanonicalTransfer.refinement_isIso i s₀ B hB M d hM N e
    U hU a t ha hat
  have hlocal := PrincipalReference.CoverTransfer.Reference.recovery U hU
    (PrincipalPoint.Fraction.family U t) (s₀ ≫ i) hcontains
    (PrincipalPoint.RelativeGeometry.common i s₀ U hU t) (PrincipalPoint.RelativeGeometry.common_affine i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.left i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.right i s₀ U hU t) V hV haV
    (GlobalTransferRecovery.left i s₀ B M v)
    (GlobalTransferRecovery.right i s₀ B M v) (n+1)
    (Survivor.exactAt i s₀ hbase B hB) (Survivor.forms (R := R)) (Survivor.adjunctionIso i s₀ hbase B hB)
    (PrincipalConcentration.parameters_outside i s₀ U hU a t hat)
    (PrincipalPoint.RelativeGeometry.common_outside i s₀ U hU t) (n+1)
  have htransfer := IntrinsicOrdered.CechTransferCoordinates.Intrinsic.comparison π V haV (n+1)
    (GlobalTransferRecovery.left i s₀ B M v)
    (GlobalTransferRecovery.right i s₀ B M v)
  exact NormalizedClassTransfer.comparison
    (LocalClass.globalCoordinate i s₀ hbase B hB) _ _ _ _ _
    (GlobalNormalization.totalIso i s₀ B)
    (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π V (n+1) (GlobalTransferRecovery.coefficientDual B M)) _
    hlocal (GlobalNormalization.normalization i s₀ hbase B hB) htransfer

variable [IsArtinianRing R] [IsLocalRing R]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev point_recovery := ConcreteCategory.congr_hom
  (recovery i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat)
    (SupportedClass.fixedPointClass i s₀ hbase B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ReferenceTransfer.Reference
