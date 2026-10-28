import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Intersections
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Cech Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates

noncomputable section

section

/-! Categorical Čech terms have the ordinary coordinates of sections on finite intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

variable {X ι : Type} [TopologicalSpace X]
  (F : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (U : ι → Opens X)

def cechIntersectionSectionIso {n : ℕ} (a : Fin (n + 1) → ι) :
    F.obj (op (∏ᶜ fun k => U (a k))) ≅ F.obj (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) :=
  F.mapIso (eqToIso (congrArg op (Betti.Cech.Intersections.cechIntersection_eq_categorical U a).symm))

def moduleCechCoordinatesIso (n : ℕ) :
    ((cechComplexFunctor U).obj F).X n ≅ ModuleCat.of ℂ (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.CechCochain F U n) :=
  Limits.Pi.mapIso (fun a => cechIntersectionSectionIso F U a) ≪≫
    ModuleCat.piIsoPi (fun a => F.obj (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)))

theorem moduleCechCoordinatesIso_hom_proj (n : ℕ) (a : Fin (n + 1) → ι) :
    (moduleCechCoordinatesIso F U n).hom ≫
        ModuleCat.ofHom (LinearMap.proj a : OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.CechCochain F U n →ₗ[ℂ]
          F.obj (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) =
      Pi.π (fun b : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k)))) a ≫
        (cechIntersectionSectionIso F U a).hom := by
  change (Limits.Pi.map (fun b => (cechIntersectionSectionIso F U b).hom) ≫
    (ModuleCat.piIsoPi (fun b => F.obj (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U b)))).hom) ≫ _ = _
  rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, Pi.map_π]

end

/-! The ordinary section coordinates preserve every Čech cosimplicial restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

variable {X ι : Type} [TopologicalSpace X]
  (F : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (U : ι → Opens X)

theorem moduleCechCoordinatesIso_hom_apply (n : ℕ)
    (x : ((cechComplexFunctor U).obj F).X n) (a : Fin (n + 1) → ι) :
    (moduleCechCoordinatesIso F U n).hom x a =
      (cechIntersectionSectionIso F U a).hom
        (Pi.π (fun b : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k)))) a x) :=
  ConcreteCategory.congr_hom (moduleCechCoordinatesIso_hom_proj F U n a) x

theorem categoricalCechMap_proj {n m : SimplexCategory} (f : n ⟶ m)
    (a : Fin (m.len + 1) → ι) :
    (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).map f) ≫
        Pi.π (fun b : Fin (m.len + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k)))) a =
      Pi.π (fun b : Fin (n.len + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k))))
          (a ∘ f.toOrderHom) ≫
        F.map (((FormalCoproduct.mk _ U).mapPower f.toOrderHom).φ a).op := by
  rw [FormalCoproduct.cosimplicialObjectFunctor_obj_map, FormalCoproduct.cech_map]
  exact Pi.lift_comp_π _ a

theorem cechIntersectionSectionIso_precomp {n m : SimplexCategory} (f : n ⟶ m)
    (a : Fin (m.len + 1) → ι) :
    F.map (((FormalCoproduct.mk _ U).mapPower f.toOrderHom).φ a).op ≫
        (cechIntersectionSectionIso F U a).hom =
      (cechIntersectionSectionIso F U (a ∘ f.toOrderHom)).hom ≫
        F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op := by
  change F.map ((Pi.lift (fun k : Fin (n.len + 1) =>
      Pi.π (fun j : Fin (m.len + 1) => U (a j)) (f.toOrderHom k))).op) ≫
      F.map (eqToHom (congrArg op (Betti.Cech.Intersections.cechIntersection_eq_categorical U a).symm)) =
    F.map (eqToHom (congrArg op
      (Betti.Cech.Intersections.cechIntersection_eq_categorical U (a ∘ f.toOrderHom)).symm)) ≫
      F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

def moduleCechCosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F ≅
      OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechCosimplicial F U :=
  NatIso.ofComponents (fun n => moduleCechCoordinatesIso F U n.len) (fun {n m} f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change (moduleCechCoordinatesIso F U m.len).hom
      ((((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).map f) x) a =
      (F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op)
        ((moduleCechCoordinatesIso F U n.len).hom x (a ∘ f.toOrderHom))
    erw [moduleCechCoordinatesIso_hom_apply, moduleCechCoordinatesIso_hom_apply]
    erw [ConcreteCategory.congr_hom (categoricalCechMap_proj F U f a) x]
    exact ConcreteCategory.congr_hom (cechIntersectionSectionIso_precomp F U f a)
      (Pi.π (fun b : Fin (n.len + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k))))
        (a ∘ f.toOrderHom) x))

def moduleCechComplexIso :
    (cechComplexFunctor U).obj F ≅ OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechComplex F U :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{0} ℂ)).mapIso
    (moduleCechCosimplicialIso F U)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates
