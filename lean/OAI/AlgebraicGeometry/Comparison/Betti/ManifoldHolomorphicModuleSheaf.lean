import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModules
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalDescent
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! # Manifold Holomorphic Module Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf

noncomputable section

/-! Actual holomorphic forms as modules over the standard holomorphic structure sheaf on every complex manifold. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

abbrev manifoldHolomorphicStructureSheaf (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] : TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  (sheafCompose (Opens.grothendieckTopology M) (forget₂ CommRingCat RingCat)).obj
    (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ)

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def manifoldHolomorphicFormModule (U : (Opens M)ᵒᵖ) (n : ℕ) :
    ModuleCat.{0} ((manifoldHolomorphicStructureSheaf E M).obj.obj U) :=
  ModuleCat.of C^∞⟮𝓘(ℂ, E), U.unop; 𝓘(ℂ), ℂ⟯ (Holomorphic.DeRhamComplex.forms E U.unop n)

def manifoldHolomorphicFormModuleMap {U V : (Opens M)ᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    manifoldHolomorphicFormModule E M U n ⟶
      (ModuleCat.restrictScalars ((manifoldHolomorphicStructureSheaf E M).obj.map f).hom).obj
        (manifoldHolomorphicFormModule E M V n) :=
  ModuleCat.ofHom (R := (manifoldHolomorphicStructureSheaf E M).obj.obj U)
    (X := manifoldHolomorphicFormModule E M U n)
    (Y := (ModuleCat.restrictScalars ((manifoldHolomorphicStructureSheaf E M).obj.map f).hom).obj
      (manifoldHolomorphicFormModule E M V n))
    { toFun := Holomorphic.HolomorphicPullback.pullback (Opens.inclusion (leOfHom f.unop))
        (contMDiff_inclusion (I := 𝓘(ℂ, E)) (leOfHom f.unop)) n
      map_add' := (Holomorphic.HolomorphicPullback.pullback (Opens.inclusion (leOfHom f.unop))
        (contMDiff_inclusion (I := 𝓘(ℂ, E)) (leOfHom f.unop)) n).map_add
      map_smul' := ManifoldHolomorphicModules.pullback_function_smul (Opens.inclusion (leOfHom f.unop))
        (contMDiff_inclusion (I := 𝓘(ℂ, E)) (leOfHom f.unop)) n }

def manifoldHolomorphicFormModulePresheaf (n : ℕ) :
    PresheafOfModules.{0} (manifoldHolomorphicStructureSheaf E M).obj where
  obj U := manifoldHolomorphicFormModule E M U n
  map f := manifoldHolomorphicFormModuleMap E M f n
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Holomorphic.HolomorphicPullback.pullback_id n a
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Holomorphic.HolomorphicPullback.pullback_comp (Opens.inclusion (leOfHom g.unop))
      (contMDiff_inclusion (I := 𝓘(ℂ, E)) (leOfHom g.unop))
      (Opens.inclusion (leOfHom f.unop))
      (contMDiff_inclusion (I := 𝓘(ℂ, E)) (leOfHom f.unop)) n a

theorem manifoldHolomorphicFormModulePresheaf_isSheaf (n : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology M)
      (manifoldHolomorphicFormModulePresheaf E M n).presheaf := by
  change Presheaf.IsSheaf (Opens.grothendieckTopology M)
    ((Holomorphic.Presheaf.presheafComplex E M).X n ⋙ forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})
  exact ((sheafCompose (Opens.grothendieckTopology M)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      ⟨(Holomorphic.Presheaf.presheafComplex E M).X n, Holomorphic.LocalDescent.holomorphicPresheaf_isSheaf E M n⟩).property

def manifoldHolomorphicFormModuleSheaf (n : ℕ) :
    SheafOfModules.{0} (manifoldHolomorphicStructureSheaf E M) where
  val := manifoldHolomorphicFormModulePresheaf E M n
  isSheaf := manifoldHolomorphicFormModulePresheaf_isSheaf E M n

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf
