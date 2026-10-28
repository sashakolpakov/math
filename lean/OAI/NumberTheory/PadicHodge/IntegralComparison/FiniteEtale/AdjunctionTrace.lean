import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtaleAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.UnitMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ModuleTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.HomUnitEvaluation

/-! # Adjunction Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionTrace

noncomputable section

/-! The actual finite étale top-form transfer is the dual of the
coefficient unit under the original projective adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem transportEvaluation {C : Type u} {D : Type v} [Category C] [Category D]
    (F : C ⥤ D) {A B N : C} {Z H : D} (a : Z ≅ H) (b : F.obj B ≅ H)
    (c : A ≅ B) (e : B ⟶ N) (E : H ⟶ F.obj N)
    (h : b.hom ≫ E = F.map e) :
    (a ≪≫ b.symm ≪≫ F.mapIso c.symm).hom ≫ F.map (c.hom ≫ e) = a.hom ≫ E := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

local instance : (FormSheafDuality.coefficients R Y X f).IsQuasicoherent :=
  FormSheafDuality.coefficient_qc R Y X f

def trace : ProjectiveFinite.EtaleAdjunction.sourceForms X Y f i g ⟶ ProjectiveCoefficient.HomLocal.formSheaf X i g := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact (Scheme.Modules.pushforward i.left).map (ModuleTrace.trace R Y X f g)

theorem normalization :
    (ProjectiveFinite.EtaleAdjunction.iso X Y f i g j B hB hg).hom ≫ trace X Y f i g =
      ProjectiveCoefficient.UnitEvaluation.dualUnit X f.left i g j B hB ≫
        (ProjectiveCoefficient.HomLocal.scalarAdjunction X i g j B hB hg).hom := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  have h := transportEvaluation (Scheme.Modules.pushforward i.left)
    (ProjectiveCoefficient.HomGlobal.iso X f.left i g j B hB hg)
    (Closed.InternalHom.iso i.left (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g))
    (FormSheafDuality.iso R Y X f g)
    (Sheaf.HomUnitEvaluation.map (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
      (SheafOfModules.unitToPushforwardObjUnit f.left.toRingCatSheafHom))
    (ProjectiveCoefficient.UnitMap.evaluation X f.left i g)
    (Closed.HomUnitEvaluation.normalization i.left
      (FormSheafDuality.coefficients R Y X f)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
      (SheafOfModules.unitToPushforwardObjUnit f.left.toRingCatSheafHom))
  exact h.trans (ProjectiveCoefficient.UnitMap.normalization X f.left i g j B hB hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionTrace
