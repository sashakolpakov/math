import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtaleAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomEvaluation

/-! # Adjunction Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionEvaluation

noncomputable section

/-! The original finite adjunction evaluates every local coefficient by
multiplying the actual source form and taking its genuine de Rham trace. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

private theorem cancel_factors {C : Type u} {D : Type v} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {Z H : D} (a : Z ≅ H) (b : F.obj B ≅ H) (c : A ≅ B) :
    (a ≪≫ b.symm ≪≫ F.mapIso c.symm).hom ≫ F.map c.hom ≫ b.hom = a.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp,
    Category.comp_id]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n+1)) (B : ℕ) (hB : n+1≤B) (hg : g≤n)
local instance coefficient_qc : (FormSheafDuality.coefficients R Y X f).IsQuasicoherent :=
  FormSheafDuality.coefficient_qc R Y X f

theorem coefficient_map :
    letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
    (ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg).hom ≫
      (Scheme.Modules.pushforward i.left).map (FormSheafDuality.iso R Y X f g).hom ≫
      (Closed.InternalHom.iso i.left (FormSheafDuality.coefficients R Y X f)
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)).hom =
    (ProjectiveCoefficient.HomGlobal.iso X f.left i g j B hB hg).hom := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact cancel_factors (Scheme.Modules.pushforward i.left)
    (ProjectiveCoefficient.HomGlobal.iso X f.left i g j B hB hg)
    (Closed.InternalHom.iso i.left (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g))
    (FormSheafDuality.iso R Y X f g)

variable (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (z : Γ(ProjectiveCoefficient.HomLocal.sourceSheaf X f.left i g j B, U)) (x : Γ(ProjectiveCoefficient.HomLocal.coefficient X f.left i, U))

include hU in
theorem hom_evaluation :
    letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) U
      ((ProjectiveCoefficient.HomGlobal.iso X f.left i g j B hB hg).hom.app U z) x =
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) (i.left ⁻¹ᵁ U)
      ((FormSheafDuality.iso R Y X f g).hom.app (i.left ⁻¹ᵁ U)
        ((ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg).hom.app U z)) x := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  have hc := congrArg (fun a => a.app U z) (coefficient_map X Y f i g j B hB hg)
  change (Closed.InternalHom.iso i.left (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)).hom.app U
    ((FormSheafDuality.iso R Y X f g).hom.app (i.left ⁻¹ᵁ U)
      ((ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg).hom.app U z)) = _ at hc
  have hi := Closed.InternalHom.iso_app i.left
    (FormSheafDuality.coefficients R Y X f)
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) U hU
    ((FormSheafDuality.iso R Y X f g).hom.app (i.left ⁻¹ᵁ U)
      ((ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg).hom.app U z))
  exact (congrArg
    (fun v => ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) U v x)
      (hc.symm.trans hi)).trans
    (Closed.InternalHom.evaluation i.left
      (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) U hU _ x)

variable (hgood : TraceBasis.Good R Y X f (i.left ⁻¹ᵁ U))

include hU hgood in
theorem trace_evaluation :
    letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R X (i.left ⁻¹ᵁ U) g).hom
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) U
        ((ProjectiveCoefficient.HomGlobal.iso X f.left i g j B hB hg).hom.app U z) x) =
    ((DeRhamSheafTrace.trace R Y X f).f g).hom.app (op (i.left ⁻¹ᵁ U))
      ((Integral.IntrinsicFormNormalization.Intrinsic.iso R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) g).hom
        ((show Γ(Y.left, f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) from x) •
          (show Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g, f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) from
            (ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg).hom.app U z))) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let a : TraceBasis.Index R Y X f := ⟨i.left ⁻¹ᵁ U,hgood⟩
  let v := (ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg).hom.app U z
  have hs := (congrArg
    (fun w => ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) (i.left ⁻¹ᵁ U) w x)
    (FormSheafDuality.iso_app R Y X f a g v)).trans
      (FormSheafDuality.sectionEquiv_evaluation R Y X f a g v x)
  exact (congrArg (Integral.IntrinsicFormNormalization.Intrinsic.iso R X (i.left ⁻¹ᵁ U) g).hom
    ((hom_evaluation X Y f i g j B hB hg U hU z x).trans hs)).trans
      (Intrinsic.EtaleFormRestriction.evaluation R Y X f a g x v)

variable (k : Fin (n+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

abbrev scalar_evaluation := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  have h := ProjectiveCoefficient.HomEvaluation.evaluation X f.left i g j B hB hg U hU k hUk z x
  have ht := trace_evaluation X Y f i g j B hB hg U hU z x hgood
  exact (congrArg (Integral.IntrinsicFormNormalization.Intrinsic.iso R X (i.left ⁻¹ᵁ U) g).hom h).symm.trans ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionEvaluation
