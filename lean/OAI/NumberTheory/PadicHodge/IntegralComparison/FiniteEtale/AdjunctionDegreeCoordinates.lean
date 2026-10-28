import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomDegreeCoordinates

/-! # Adjunction Degree Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionDegreeCoordinates

noncomputable section

/-! The same explicit codimension transport is used by finite top-form
adjunction, coefficient evaluation, and the genuine de Rham trace. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (hc : c=n-g) (j : Fin (n+1)) (B : ℕ) (hB : n+1≤B) (hg : g≤n)
local instance coefficient_qc : (FormSheafDuality.coefficients R Y X f).IsQuasicoherent :=
  FormSheafDuality.coefficient_qc R Y X f

def iso : (ProjectiveCoefficient.HomLocal.coefficientDual X f.left i j B).homology c ≅
    (Scheme.Modules.pushforward i.left).obj
      ((Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g)) :=
  eqToIso (congrArg (fun d => (ProjectiveCoefficient.HomLocal.coefficientDual X f.left i j B).homology d) hc) ≪≫
    ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg

theorem coefficient_map :
    letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
    (iso X Y f i g c hc j B hB hg).hom ≫
      (Scheme.Modules.pushforward i.left).map (FormSheafDuality.iso R Y X f g).hom ≫
      (Closed.InternalHom.iso i.left (FormSheafDuality.coefficients R Y X f)
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)).hom =
    (ProjectiveCoefficient.HomDegreeCoordinates.iso X f.left i g c hc j B hB hg).hom := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  have h := AdjunctionEvaluation.coefficient_map X Y f i g j B hB hg
  simpa only [iso, ProjectiveCoefficient.HomDegreeCoordinates.iso,
    Iso.trans_hom, Category.assoc] using congrArg
      (fun a => (eqToIso (congrArg
        (fun d => (ProjectiveCoefficient.HomLocal.coefficientDual X f.left i j B).homology d) hc)).hom ≫ a) h

variable (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (z : Γ((ProjectiveCoefficient.HomLocal.coefficientDual X f.left i j B).homology c, U))
  (x : Γ(ProjectiveCoefficient.HomLocal.coefficient X f.left i, U))
  (hgood : TraceBasis.Good R Y X f (i.left ⁻¹ᵁ U))

include hU hgood in
theorem trace_evaluation :
    letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R X (i.left ⁻¹ᵁ U) g).hom
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) U
        ((ProjectiveCoefficient.HomDegreeCoordinates.iso X f.left i g c hc j B hB hg).hom.app U z) x) =
    ((DeRhamSheafTrace.trace R Y X f).f g).hom.app (op (i.left ⁻¹ᵁ U))
      ((Integral.IntrinsicFormNormalization.Intrinsic.iso R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) g).hom
        ((show Γ(Y.left, f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) from x) •
          (show Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g, f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) from
            (iso X Y f i g c hc j B hB hg).hom.app U z))) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact AdjunctionEvaluation.trace_evaluation X Y f i g j B hB hg U hU
    ((eqToIso (congrArg (fun d => (ProjectiveCoefficient.HomLocal.coefficientDual X f.left i j B).homology d) hc)).hom.app U z)
    x hgood

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionDegreeCoordinates
