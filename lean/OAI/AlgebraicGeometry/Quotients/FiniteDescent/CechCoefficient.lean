import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechShortComplex
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseModule

/-! # Cech Coefficient -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoefficient

noncomputable section

/-! Ordinary Cech short complexes are functorial in their actual sheaf
coefficients. In particular, a line-bundle trivialization acts componentwise. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechCoefficientFunctor

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X)
variable {F G : TopCat.Sheaf (ModuleCat.{u} R) X} (a : F ⟶ G)

def zero : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 F U →ₗ[R] OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 G U :=
  LinearMap.pi fun i => (a.hom.app (op (U i))).hom.comp (LinearMap.proj i)

def one : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 F U →ₗ[R] OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 G U where
  toFun z i j := a.hom.app (op (U i ⊓ U j)) (z i j)
  map_add' z w := by funext i j; exact map_add _ _ _
  map_smul' r z := by funext i j; exact map_smul _ _ _

def two : OpenCechShortComplex.Construction.CubeCech.openModuleCechC2 F U →ₗ[R] OpenCechShortComplex.Construction.CubeCech.openModuleCechC2 G U where
  toFun z i j k := a.hom.app (op ((U i ⊓ U j) ⊓ U k)) (z i j k)
  map_add' z w := by funext i j k; exact map_add _ _ _
  map_smul' r z := by funext i j k; exact map_smul _ _ _

theorem restrict {V W : Opens X} (h : W ≤ V) (s : F.obj.obj (op V)) :
    a.hom.app (op W) (F.obj.map (homOfLE h).op s) =
      G.obj.map (homOfLE h).op (a.hom.app (op V) s) :=
  ConcreteCategory.congr_hom (a.hom.naturality (homOfLE h).op) s

theorem differential_zero (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 F U) :
    one U a (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F U z) = OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 G U (zero U a z) := by
  funext i j
  change a.hom.app (op (U i ⊓ U j))
    (F.obj.map (homOfLE inf_le_right).op (z j) -
      F.obj.map (homOfLE inf_le_left).op (z i)) = _
  rw [map_sub, restrict, restrict]
  rfl

theorem differential_one (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 F U) :
    two U a (OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 F U z) = OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 G U (one U a z) := by
  funext i j k
  change a.hom.app (op ((U i ⊓ U j) ⊓ U k))
    (F.obj.map (homOfLE _).op (z i j) + F.obj.map (homOfLE _).op (z j k) -
      F.obj.map (homOfLE _).op (z i k)) = _
  rw [map_sub, map_add, restrict, restrict, restrict]
  rfl

def map : OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex F U ⟶ OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex G U where
  τ₁ := ModuleCat.ofHom (zero U a)
  τ₂ := ModuleCat.ofHom (one U a)
  τ₃ := ModuleCat.ofHom (two U a)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (differential_zero U a z).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (differential_one U a z).symm

def functor : TopCat.Sheaf (ModuleCat.{u} R) X ⥤ ShortComplex (ModuleCat.{u} R) where
  obj F := OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex F U
  map a := CechCoefficientFunctor.map U a
  map_id F := by
    apply ShortComplex.hom_ext <;> apply ModuleCat.hom_ext <;> rfl
  map_comp a b := by
    apply ShortComplex.hom_ext <;> apply ModuleCat.hom_ext <;> rfl

def moduleSheafFunctor {X S : Scheme.{u}} (π : X ⟶ S) :
    X.Modules ⥤ TopCat.Sheaf (ModuleCat.{u} Γ(S, ⊤)) (Scheme.forgetToTop.obj X) where
  obj M := BaseModule.Construction.BaseModuleSheaf.sheaf π M
  map a := ⟨(SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map a⟩
  map_id M := by apply Sheaf.hom_ext; exact (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map_id M
  map_comp a b := by apply Sheaf.hom_ext; exact (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map_comp a b

def moduleFunctor {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} (U : ι → X.Opens) :
    X.Modules ⥤ ShortComplex (ModuleCat.{u} Γ(S, ⊤)) := moduleSheafFunctor π ⋙ functor U

end Construction.CechCoefficientFunctor

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoefficient
