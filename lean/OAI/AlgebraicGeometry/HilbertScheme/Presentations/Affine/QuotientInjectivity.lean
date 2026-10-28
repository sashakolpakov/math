import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientClassifyingMap
import Mathlib.RingTheory.LocalProperties.Submodule

/-! # Quotient Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine

noncomputable section

/-! The global Grassmannian classifying map recovers the original quotient submodule. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {R : CommRingCat.{u}} {N : Module.Grassmannian R (ν → R) (Fintype.card ι)}

def QuotientClassifyingCharts.Grassmannian.PrincipalQuotientChart.atPrimeMap (D : QuotientClassifyingCharts.Grassmannian.PrincipalQuotientChart R N)
    (p : PrimeSpectrum R) (hr : D.denominator ∉ p.asIdeal) :
    Relative.AffinePoints.relativeAffineScheme R (Localization.AtPrime p.asIdeal) ⟶ D.scheme := by
  let φ : Localization.Away D.denominator →ₐ[R] Localization.AtPrime p.asIdeal :=
    IsLocalization.Away.liftAlgHom D.denominator
      (f := Algebra.ofId R (Localization.AtPrime p.asIdeal))
      (IsLocalization.map_units (M := p.asIdeal.primeCompl)
        (Localization.AtPrime p.asIdeal) ⟨D.denominator, hr⟩)
  exact (algSpec R).map (CommAlgCat.ofHom φ).op

theorem QuotientInjectivity.Grassmannian.quotientClassifyingMap_local_kernel_eq
    (N M : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (h : QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N = QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R M) (p : PrimeSpectrum R) :
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Localization.AtPrime p.asIdeal)) N.toSubmodule =
      Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Localization.AtPrime p.asIdeal)) M.toSubmodule := by
  let D := (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val
  let E := (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R M p).val
  let T := Relative.AffinePoints.relativeAffineScheme R (Localization.AtPrime p.asIdeal)
  let f : T ⟶ D.scheme := D.atPrimeMap p (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).property
  let g : T ⟶ E.scheme := E.atPrimeMap p (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R M p).property
  have he : f ≫ D.classifyingMap = g ≫ E.classifyingMap := by
    apply (Over.forget (Spec R)).map_injective
    change f.left ≫ D.classifyingMap.left = g.left ≫ E.classifyingMap.left
    have hN : f.left ≫ D.classifyingMap.left = T.hom ≫ QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N :=
      (congrArg (fun k => f.left ≫ k) (QuotientClassifyingMap.Grassmannian.quotientClassifyingMap_on_chart R N D).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N) f.w))
    have hM : g.left ≫ E.classifyingMap.left = T.hom ≫ QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R M :=
      (congrArg (fun k => g.left ≫ k) (QuotientClassifyingMap.Grassmannian.quotientClassifyingMap_on_chart R M E).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R M) g.w))
    exact hN.trans ((congrArg (fun k => T.hom ≫ k) h).trans hM.symm)
  rw [D.classifyingMap_comp, E.classifyingMap_comp, Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap_eq_iff,
    D.pointMatrix_kernel, E.pointMatrix_kernel] at he
  let e := Relative.AffinePoints.relativeAffineGlobalEquiv R (Localization.AtPrime p.asIdeal)
  have hc : e.toRingHom.comp (algebraMap R (Localization.AtPrime p.asIdeal)) =
      algebraMap R (Relative.AffinePoints.relativeGlobalAlgebra R T) := by
    ext r
    exact e.commutes r
  change Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Relative.AffinePoints.relativeGlobalAlgebra R T)) N.toSubmodule =
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Relative.AffinePoints.relativeGlobalAlgebra R T)) M.toSubmodule at he
  rw [← hc, Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp, Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp] at he
  exact Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_injective e.toRingEquiv he

theorem QuotientInjectivity.Grassmannian.quotientClassifyingMap_injective :
    Function.Injective (QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (ι := ι) (ν := ν) R) := by
  intro N M h
  apply Module.Grassmannian.ext
  apply Submodule.eq_of_localization_maximal
    (fun p _ => Localization.AtPrime p)
    (fun p _ => ν → Localization.AtPrime p)
    (fun p _ => Localized.QuotientCoordinates.Grassmannian.coordinateLocalization (ν := ν) p.primeCompl)
  intro p _
  rw [Submodule.localized'_eq_span, Submodule.localized'_eq_span]
  exact QuotientInjectivity.Grassmannian.quotientClassifyingMap_local_kernel_eq N M h ⟨p, inferInstance⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine
