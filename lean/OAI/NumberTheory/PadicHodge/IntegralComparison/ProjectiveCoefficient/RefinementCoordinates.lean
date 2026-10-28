import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DualRefinementResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CoefficientLocalClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFraction

/-! # Refinement Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.RefinementCoordinates

noncomputable section

/-! The actual coherent coefficient transfer retains its original
right/inverse-left maps in principal dual coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ} {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra
  ProjectivePoint.Survivor.coefficient_qc ProjectivePoint.Survivor.coefficient_finite
variable (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2≤B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (v : M ⟶ ProjectivePoint.Survivor.coefficient i s₀)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  {κ : Type u} [LinearOrder κ] (W : κ → Principal.SectionPresheaf.Index U) (q : ℕ)

abbrev leftChain := (Projective.NegativeRefinement.leftHom M (ProjectivePoint.Survivor.coefficient i s₀)
  (ProjectivePoint.Survivor.chart (R := R)) B v).chainMap
abbrev rightChain := (Projective.NegativeRefinement.rightHom M (ProjectivePoint.Survivor.coefficient i s₀)
  (ProjectivePoint.Survivor.chart (R := R)) B v).chainMap
abbrev nativeLeft := Principal.DualRefinementMap.nativeMap U hU
  (ProjectivePoint.ScalarFraction.line (R := R) (n := n)) (leftChain i s₀ B M v)
abbrev nativeRight := Principal.DualRefinementMap.nativeMap U hU
  (ProjectivePoint.ScalarFraction.line (R := R) (n := n)) (rightChain i s₀ B M v)

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem originalLeft_isIso :
    IsIso ((PrincipalReference.Concentration.Reference.functor U hU W q).map
      ((Affine.LocalDualInvariance.functor
        (ProjectivePoint.ScalarFraction.line (R := R) (n := n))).map
          (leftChain i s₀ B M v).op)) := by
  let (a : ℕ) : ((ProjectivePoint.GlobalTransferRecovery.coefficientDual B M).X a).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (ProjectivePoint.Survivor.chart (R := R)) B (n+2) hB a
  let (a : ℕ) : ((ProjectivePoint.GlobalTransferRecovery.commonDual i s₀ B M v).X a).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (ProjectivePoint.Survivor.coefficient i s₀)
      (ProjectivePoint.Survivor.chart (R := R)) B (n+2) hB v a
  let := ProjectiveRefinement.DualMap.left_quasiIso M (ProjectivePoint.Survivor.coefficient i s₀)
    (ProjectivePoint.Survivor.chart (R := R)) B (n+2) hB v
  exact Principal.RelativeTransfer.left_isIso U hU W q
    (ProjectivePoint.GlobalTransferRecovery.left i s₀ B M v)

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem nativeLeft_isIso :
    IsIso ((Supported.CechHomotopyEquivalence.functor W q).map
      (nativeLeft i s₀ B M v U hU)) := by
  let := originalLeft_isIso i s₀ B hB M v U hU W q
  exact Principal.DualRefinementMap.isIso U hU W q
    (ProjectivePoint.ScalarFraction.line (R := R) (n := n)) (leftChain i s₀ B M v)

variable {c g : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U))
  (hst : KoszulPartial.Resolution.pointIdeal
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U) s t = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  (hcg : c+g=n+1)
  {L : CochainComplex ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤
    ModuleCat.{u} Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U)) ℕ}
  (a : Principal.Koszul.Comparison.nativeComplex U hU
    (ProjectivePoint.ScalarFraction.line (R := R) (n := n))
    (Projective.NegativeResolution.complex M (ProjectivePoint.Survivor.chart (R := R)) B) ⟶ L)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
 theorem comparison :
    letI := nativeLeft_isIso i s₀ B hB M v U hU (PrincipalPoint.Fraction.family U t) (c+g)
    (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
      (Principal.IntrinsicDualCoordinates.Intrinsic.map U hU
        (ProjectivePoint.ScalarFraction.line (R := R) (n := n))
        (Projective.NegativeResolution.complex M (ProjectivePoint.Survivor.chart (R := R)) B) a)
      (ProjectivePoint.CoefficientLocalClass.value i s₀ hbase B hB M v U hU s t hst hcg) =
    (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map a
      (((Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
        (nativeRight i s₀ B M v U hU) ≫
          inv ((Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
            (nativeLeft i s₀ B M v U hU)))
        (ProjectivePoint.LocalCoordinates.pointAt i s₀ hbase B hB U hU s t hst hcg)) := by
  let := originalLeft_isIso i s₀ B hB M v U hU (PrincipalPoint.Fraction.family U t) (c+g)
  let := nativeLeft_isIso i s₀ B hB M v U hU (PrincipalPoint.Fraction.family U t) (c+g)
  convert Principal.DualRefinementResidue.apply U hU (PrincipalPoint.Fraction.family U t) (c+g)
    (ProjectivePoint.ScalarFraction.line (R := R) (n := n))
    (leftChain i s₀ B M v) (rightChain i s₀ B M v) a
    (ProjectivePoint.LocalCoordinates.pointAt i s₀ hbase B hB U hU s t hst hcg) using 1 <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.RefinementCoordinates
