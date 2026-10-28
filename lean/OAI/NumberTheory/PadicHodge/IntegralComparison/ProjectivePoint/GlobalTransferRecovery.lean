import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.GlobalTransferRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms

/-! # Global Transfer Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalTransferRecovery

noncomputable section

/-! The exact fixed projective point class, localized on its parameter
cover and mapped by the original common resolution, recovers the
corresponding global resolution transfer. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion i] (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (v : M ⟶ Survivor.coefficient i s₀)
attribute [local instance] Survivor.coefficient_qc
  Survivor.coefficient_finite

abbrev coefficientDual := (ProjectiveRefinement.DualMap.dualFunctor (R := R)
  (Survivor.chart (R := R) (n := n)) (n+2)).obj
    (op (Projective.NegativeResolution.complex M (Survivor.chart (R := R)) B))
abbrev commonDual := (ProjectiveRefinement.DualMap.dualFunctor (R := R)
  (Survivor.chart (R := R) (n := n)) (n+2)).obj
    (op (Projective.NegativeRefinement.complex M (Survivor.coefficient i s₀) (Survivor.chart (R := R)) B v))
abbrev left := ProjectiveRefinement.DualMap.leftMap M (Survivor.coefficient i s₀)
  (Survivor.chart (R := R)) B (n+2) v
abbrev right := ProjectiveRefinement.DualMap.rightMap M (Survivor.coefficient i s₀)
  (Survivor.chart (R := R)) B (n+2) v

variable (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  {c g : ℕ} (a : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hat : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) a t =
    (s₀ ≫ i).ker.ideal ⟨U, hU⟩)
  {κ ν : Type u} [LinearOrder κ] [LinearOrder ν]
  (W : κ → (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens)
  (hW : ∀ k, IsAffineOpen (W k))
  (J : ν → (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens)
  (hJ : ∀ k, IsAffineOpen (J k))
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk (ULift.{u} (Fin g))
    (Principal.RelativeConcentration.family U hU (PrincipalPoint.Fraction.family U t)))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ W)
  (hWO : ∀ k, W k ≤ SectionIdealPuncturedCover.outside (s₀ ≫ i).ker)
  (hJO : ∀ k, J k ≤ SectionIdealPuncturedCover.outside (s₀ ≫ i).ker)
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU) W J s
    (Relative.AdditiveCechConcentration.coefficients (coefficientDual B M)) (n+1))]

abbrev localize_recovery := by
  letI : ∀ q, ((coefficientDual B M).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
  letI : ∀ q, ((Survivor.dual i s₀ B).X q).IsQuasicoherent :=
    PrincipalConcentration.terms_qc i s₀ B hB
  letI : ∀ q, ((commonDual i s₀ B M v).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i s₀)
      (Survivor.chart (R := R)) B (n+2) hB v
  letI := ProjectiveRefinement.DualMap.left_quasiIso M (Survivor.coefficient i s₀)
    (Survivor.chart (R := R)) B (n+2) hB v
  exact Principal.GlobalTransferRecovery.recovery U hU (PrincipalPoint.Fraction.family U t)
    W hW J hJ r s (left i s₀ B M v) (right i s₀ B M v) (n+1)
    (Survivor.exactAt i s₀ hbase B hB) (s₀ ≫ i) (Survivor.forms (R := R))
    (Survivor.adjunctionIso i s₀ hbase B hB)
    (PrincipalConcentration.parameters_outside i s₀ U hU a t hat)
    hWO hJO (n+1)

abbrev map_recovery := congrArg
  (fun a => LocalClass.globalCoordinate i s₀ hbase B hB ≫ a)
    (localize_recovery i s₀ hbase B hB M v U hU a t hat W hW J hJ r s hWO hJO)

variable [IsArtinianRing R] [IsLocalRing R]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev point_recovery := ConcreteCategory.congr_hom
  (map_recovery i s₀ hbase B hB M v U hU a t hat W hW J hJ r s hWO hJO)
    (SupportedClass.fixedPointClass i s₀ hbase B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalTransferRecovery
