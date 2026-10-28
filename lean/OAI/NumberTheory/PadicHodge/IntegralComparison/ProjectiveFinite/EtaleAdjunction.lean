import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.InternalHom

/-! # Etale Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtaleAdjunction

noncomputable section

/-! The dual resolution of the actual finite étale coefficient algebra
is canonically the actual iterated direct image of source top forms.
Only the target is embedded in projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

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
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

abbrev sourceForms := (Scheme.Modules.pushforward i.left).obj
  ((Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g))

def iso : ProjectiveCoefficient.HomLocal.sourceSheaf X f.left i g j B ≅ sourceForms X Y f i g := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  letI : (FiniteEtale.FormSheafDuality.coefficients R Y X f).IsQuasicoherent :=
    FiniteEtale.FormSheafDuality.coefficient_qc R Y X f
  exact ProjectiveCoefficient.HomGlobal.iso X f.left i g j B hB hg ≪≫
    (Closed.InternalHom.iso i.left (FiniteEtale.FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)).symm ≪≫
    (Scheme.Modules.pushforward i.left).mapIso (FiniteEtale.FormSheafDuality.iso R Y X f g).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtaleAdjunction
