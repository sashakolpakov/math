import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormMaps
import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-! # De Rham Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamPresheaf

noncomputable section

/-!
# IntegralComparison: the actual de Rham differential is a morphism of Frobenius module presheaves
-/

open _root_.CategoryTheory

universe u v w

variable (k : Type u) [Field k] [Fintype k] {C : Type v} [Category.{w} C]
  (H : Cᵒᵖ ⥤ CommAlgCat.{u} k)

abbrev rings : Cᵒᵖ ⥤ RingCat.{u} :=
  H ⋙ forget₂ (CommAlgCat.{u} k) CommRingCat ⋙ forget₂ CommRingCat RingCat

def forms (n : ℕ) : PresheafOfModules.{u} (rings k H) where
  obj U := DeRhamComplex.forms k (H.obj U) n
  map f := FormMaps.map (H.map f) n
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map (𝟙 U)) n ω = ω
    rw [H.map_id]
    exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_id (H.obj U) n ω
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map (f ≫ g)) n ω =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map g) n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map f) n ω)
    rw [H.map_comp]
    exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (H.map f) (H.map g) n ω

def differential (n : ℕ) : forms k H n ⟶ forms k H (n + 1) where
  app U := DeRhamComplex.differential k (H.obj U) n
  naturality f := FormMaps.differential (H.map f) n

theorem differential_square (n : ℕ) : differential k H n ≫ differential k H (n + 1) = 0 := by
  apply PresheafOfModules.hom_ext
  intro U
  exact DeRhamComplex.differential_square k (H.obj U) n

def complex : CochainComplex (PresheafOfModules.{u} (rings k H)) ℕ :=
  CochainComplex.of (forms k H) (differential k H) (differential_square k H)

def evaluationIso (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation (rings k H) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (complex k H) ≅ DeRhamComplex.complex k (H.obj U) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      change (𝟙 _) ≫ (DeRhamComplex.complex k (H.obj U)).d i (i + 1) =
        (PresheafOfModules.evaluation (rings k H) U).map ((complex k H).d i (i + 1)) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      dsimp only [complex, DeRhamComplex.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamPresheaf
