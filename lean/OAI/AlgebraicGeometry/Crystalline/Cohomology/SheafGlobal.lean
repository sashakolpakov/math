import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Sheaf Global -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal.SheafGlobalExtVanishing

noncomputable section

/-!
# From exact global sections of a resolution to the original Ext groups

Maps from the constant rank-one sheaf are global sections. The existing
injective-resolution representatives for Ext therefore turn exactness of
the global-section complex into positive Ext vanishing.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
  [HasGlobalSectionsFunctor J (ModuleCat.{w} R)]

local instance global_additive : (Sheaf.Γ J (ModuleCat.{w} R)).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance constant_additive : (constantSheaf J (ModuleCat.{w} R)).Additive :=
  (constantSheafΓAdj J (ModuleCat.{w} R)).left_adjoint_additive

def rankOne : Sheaf J (ModuleCat.{w} R) :=
  (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)

def homEquiv (F : Sheaf J (ModuleCat.{w} R)) :
    (rankOne J R ⟶ F) ≃+ (Sheaf.Γ J (ModuleCat.{w} R)).obj F :=
  ((constantSheafΓAdj J (ModuleCat.{w} R)).homAddEquiv (ModuleCat.of R R) F).trans
    (ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toAddEquiv)

theorem homEquiv_natural {F G : Sheaf J (ModuleCat.{w} R)}
    (f : rankOne J R ⟶ F) (g : F ⟶ G) :
    homEquiv J R G (f ≫ g) = (Sheaf.Γ J (ModuleCat.{w} R)).map g (homEquiv J R F f) :=
  ConcreteCategory.congr_hom ((constantSheafΓAdj J (ModuleCat.{w} R)).homEquiv_naturality_right f g) 1

variable [HasExt.{e} (Sheaf J (ModuleCat.{w} R))]
  (F : Sheaf J (ModuleCat.{w} R)) (I : InjectiveResolution F) (n : ℕ)

theorem ext_eq_zero
    (hI : (((Sheaf.Γ J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1))
    (α : Abelian.Ext (rankOne J R) F (n + 1)) : α = 0 := by
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (n + 2) rfl
  let x := homEquiv J R (I.cocomplex.X (n + 1)) f
  have hx : (Sheaf.Γ J (ModuleCat.{w} R)).map (I.cocomplex.d (n + 1) (n + 2)) x = 0 := by
    rw [← homEquiv_natural, hf, map_zero]
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at hI
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hI x hx
  change (Sheaf.Γ J (ModuleCat.{w} R)).obj (I.cocomplex.X n) at y
  apply (I.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr
  refine ⟨(homEquiv J R (I.cocomplex.X n)).symm y, ?_⟩
  apply (homEquiv J R (I.cocomplex.X (n + 1))).injective
  rw [homEquiv_natural]
  exact (congrArg ((Sheaf.Γ J (ModuleCat.{w} R)).map (I.cocomplex.d n (n + 1)))
    ((homEquiv J R (I.cocomplex.X n)).apply_symm_apply y)).trans hy

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal.SheafGlobalExtVanishing
