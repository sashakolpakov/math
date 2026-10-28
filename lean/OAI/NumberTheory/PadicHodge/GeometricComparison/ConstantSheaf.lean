import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineSectionComplex
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Constant Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections

noncomputable section

/-! The constant rank-one sheaf represents actual global sections, linearly and naturally. -/

open _root_.CategoryTheory Limits Opposite

variable (R : Type) [CommRing R] (X : TopCat)

abbrev Sheaves := Sheaf (Opens.grothendieckTopology X) (ModuleCat R)

abbrev coefficient : Sheaves R X :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat R)).obj (ModuleCat.of R R)

def equiv (F : Sheaves R X) : (coefficient R X ⟶ F) ≃ F.obj.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat R)
    isTerminalTop).homEquiv (ModuleCat.of R R) F).trans
      ((ModuleCat.homLinearEquiv (R := R) (S := R)).toEquiv.trans
        (LinearMap.ringLmapEquivSelf R R _).toEquiv)

theorem equiv_apply (F : Sheaves R X) (f : coefficient R X ⟶ F) :
    equiv R X F f = ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat R)
      isTerminalTop).homEquiv (ModuleCat.of R R) F f) 1 := rfl

def linearEquiv (F : Sheaves R X) : (coefficient R X ⟶ F) ≃ₗ[R] F.obj.obj (op ⊤) where
  toEquiv := equiv R X F
  map_add' f g := by
    change equiv R X F (f + g) = equiv R X F f + equiv R X F g
    simp only [equiv_apply, Adjunction.homEquiv_unit]
    rfl
  map_smul' r f := by
    change equiv R X F (r • f) = r • equiv R X F f
    simp only [equiv_apply, Adjunction.homEquiv_unit]
    rfl

theorem naturality {F G : Sheaves R X} (f : coefficient R X ⟶ F) (g : F ⟶ G) :
    linearEquiv R X G (f ≫ g) = g.hom.app (op ⊤) (linearEquiv R X F f) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat R) isTerminalTop
  change (adj.homEquiv _ G (f ≫ g)) 1 = _
  rw [adj.homEquiv_naturality_right]
  rfl

def complexIso {ι : Type} (c : ComplexShape ι) (K : HomologicalComplex (Sheaves R X) c) :
    ((((linearCoyoneda R (Sheaves R X)).obj (op (coefficient R X))).mapHomologicalComplex c).obj K) ≅
      ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat R)).obj
        (op ⊤)).mapHomologicalComplex c).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (linearEquiv R X (K.X n)).toModuleIso)
    (fun i j _ => by
      ext f
      exact naturality R X f (K.d i j))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections
