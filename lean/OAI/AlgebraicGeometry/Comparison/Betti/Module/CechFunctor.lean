import OAI.AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates
import OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor

/-! # Cech Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.CechFunctor

noncomputable section

/-! The categorical and ordinary Čech complexes agree naturally in the coefficient presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X ι : Type} [TopologicalSpace X] (U : ι → Opens X)
  {F G : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ} (α : F ⟶ G)

theorem cechIntersectionSectionIso_naturality {n : ℕ} (a : Fin (n + 1) → ι) :
    α.app (op (∏ᶜ fun k => U (a k))) ≫ (CechCoordinates.cechIntersectionSectionIso G U a).hom =
      (CechCoordinates.cechIntersectionSectionIso F U a).hom ≫ α.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) :=
  (α.naturality (eqToHom (congrArg op (Cech.Intersections.cechIntersection_eq_categorical U a).symm))).symm

theorem moduleCechCoordinatesIso_naturality (n : ℕ) :
    ((cechComplexFunctor U).map α).f n ≫ (CechCoordinates.moduleCechCoordinatesIso G U n).hom =
      (CechCoordinates.moduleCechCoordinatesIso F U n).hom ≫
        ModuleCat.ofHom (AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U α n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext a
  change (CechCoordinates.moduleCechCoordinatesIso G U n).hom (((cechComplexFunctor U).map α).f n x) a =
    (α.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) ((CechCoordinates.moduleCechCoordinatesIso F U n).hom x a)
  erw [CechCoordinates.moduleCechCoordinatesIso_hom_apply, CechCoordinates.moduleCechCoordinatesIso_hom_apply]
  have hm : ((cechComplexFunctor U).map α).f n ≫
      Pi.π (fun b : Fin (n + 1) → ι => G.obj (op (∏ᶜ fun k => U (b k)))) a =
    Pi.π (fun b : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k)))) a ≫
      α.app (op (∏ᶜ fun k => U (a k))) :=
    Pi.map_π (fun b : Fin (n + 1) → ι => α.app (op (∏ᶜ fun k => U (b k)))) a
  erw [ConcreteCategory.congr_hom hm x]
  exact ConcreteCategory.congr_hom (cechIntersectionSectionIso_naturality U α a)
    (Pi.π (fun b : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k)))) a x)

def moduleCechFunctorIso :
    cechComplexFunctor U ≅ AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U :=
  NatIso.ofComponents (fun F => CechCoordinates.moduleCechComplexIso F U) (fun α => by
    apply HomologicalComplex.Hom.ext
    funext n
    exact moduleCechCoordinatesIso_naturality U α n)

instance categoricalModuleCechFunctor_additive :
    (cechComplexFunctor (A := ModuleCat.{0} ℂ) U).Additive :=
  Functor.additive_of_iso (moduleCechFunctorIso U).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.CechFunctor
