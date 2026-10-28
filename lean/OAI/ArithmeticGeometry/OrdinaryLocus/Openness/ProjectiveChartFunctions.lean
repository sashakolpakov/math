import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions

/-! # Projective Chart Functions -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartFunctions.Construction

noncomputable section

/-! Pullback of projective affine coordinates along a section chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem projectiveBasicOpenIso_inv_appTop (i : Fin (n + 1)) :
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) Nat.zero_lt_one).inv.appTop =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)).topIso.hom ≫
        (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
          (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) Nat.zero_lt_one).inv ≫
          (Scheme.ΓSpecIso (.of (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i))).inv := by
  let e := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
    (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) Nat.zero_lt_one
  have : IsIso e.hom.appTop := (Scheme.Γ.mapIso e.op).isIso_hom
  apply (cancel_mono e.hom.appTop).mp
  rw [← Scheme.Hom.comp_appTop]
  change (e.hom ≫ e.inv).appTop = _
  rw [e.hom_inv_id, Scheme.Hom.id_appTop]
  dsimp only [e]
  rw [Proj.basicOpenIsoSpec_hom]
  dsimp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  rw [← Proj.basicOpenIsoAway_hom _ _ (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) Nat.zero_lt_one]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

def projectiveChartToOpen {T : Scheme.{u}} (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    T ⟶ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)).toScheme :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi)) ≫
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) Nat.zero_lt_one).inv

theorem projectiveChartToOpen_ι {T : Scheme.{u}} (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    projectiveChartToOpen c v i hi ≫
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)).ι =
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap c v i hi := by
  simp only [projectiveChartToOpen, AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap, Proj.awayι, Category.assoc]
  rfl

theorem projectiveChartToOpen_appTop {T : Scheme.{u}} (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) Nat.zero_lt_one).hom ≫
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)).topIso.inv ≫
        (projectiveChartToOpen c v i hi).appTop =
          CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) := by
  rw [projectiveChartToOpen, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    projectiveBasicOpenIso_inv_appTop, Scheme.toSpecΓ_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Scheme.ΓSpecIso_naturality]

theorem projectiveChartToOpen_coordinate {T : Scheme.{u}} (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) (k : Fin (n + 1)) :
    (projectiveChartToOpen c v i hi).appTop
      ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)).topIso.inv
        (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)) = v k := by
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
  have h := ConcreteCategory.congr_hom (projectiveChartToOpen_appTop c v i hi)
    (HomogeneousLocalization.Away.isLocalizationElem
      (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R k))
  apply h.trans
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi _ = v k
  simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one] using
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation_coordinate c v i hi k

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartFunctions.Construction
