import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso

/-! # Nonempty Cech Extra -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra.NonemptyCechNerve

noncomputable section

/-!
# The augmented Čech complex of a nonempty set

The simplices are ordered tuples. Inserting a chosen element gives an
extra degeneracy, hence the free-module augmentation is a homotopy
equivalence. The augmentation itself is canonical and natural in the set.
-/

open _root_.CategoryTheory Opposite Simplicial _root_.AlgebraicTopology

universe u

def nerve (S : Type u) : SimplicialObject (Type u) where
  obj n := ToType n.unop → S
  map f := ↾fun v => v ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

def augmented (S : Type u) : SimplicialObject.Augmented (Type u) where
  left := nerve S
  right := PUnit
  hom :=
    { app _ := ↾fun _ => PUnit.unit
      naturality _ _ _ := rfl }

def map {S T : Type u} (f : S → T) : augmented S ⟶ augmented T where
  left :=
    { app _ := ↾fun v => f ∘ v
      naturality _ _ _ := rfl }
  right := 𝟙 _
  w := rfl

def augmentedFunctor : Type u ⥤ SimplicialObject.Augmented (Type u) where
  obj := augmented
  map f := NonemptyCechNerve.map f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Inserting a fixed point contracts the tuple nerve. -/
def extraDegeneracy (S : Type u) (s : S) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmented S) where
  s' := ↾fun _ _ => s
  s _ := ↾fun v => Fin.cons s v
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro v
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro v
    funext i
    change Fin (n + 1) → S at v
    change Fin (n + 1) at i
    change (Fin.cons s v : Fin (n + 2) → S) (Fin.succAbove 0 i) = v i
    simp
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro v
    funext j
    change Fin (n + 2) → S at v
    change Fin (n + 2) at j
    change (Fin.cons s v : Fin (n + 3) → S) (i.succ.succAbove j) =
      (Fin.cons s (fun a => v (i.succAbove a)) : Fin (n + 2) → S) j
    exact Fin.cases (by simp) (fun j => by simp) j
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro v
    funext j
    change Fin (n + 1) → S at v
    change Fin (n + 3) at j
    change (Fin.cons s v : Fin (n + 2) → S) (i.succ.predAbove j) =
      (Fin.cons s (fun a => v (i.predAbove a)) : Fin (n + 3) → S) j
    exact Fin.cases (by simp) (fun j => by simp) j

variable (R : Type u) [CommRing R]

def moduleFunctor : Type u ⥤ SimplicialObject.Augmented (ModuleCat R) :=
  augmentedFunctor ⋙ (SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free R)

def complexFunctor : Type u ⥤ ChainComplex (ModuleCat R) ℕ :=
  moduleFunctor R ⋙ SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex (ModuleCat R)

def constantFunctor : Type u ⥤ ChainComplex (ModuleCat R) ℕ :=
  moduleFunctor R ⋙ SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ (ModuleCat R)

def constantFunctorIso : constantFunctor R ≅
    (Functor.const (Type u)).obj
      ((ChainComplex.single₀ (ModuleCat R)).obj ((ModuleCat.free R).obj PUnit)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro S T f
    change ((ChainComplex.single₀ (ModuleCat R)).map ((ModuleCat.free R).map (𝟙 PUnit))) ≫ 𝟙 _ =
      𝟙 _ ≫ 𝟙 _
    simp)

/-- The canonical augmentation, without any choice of a point. -/
def augmentation : complexFunctor R ⟶ constantFunctor R :=
  Functor.whiskerLeft (moduleFunctor R) AlternatingFaceMapComplex.ε

def homotopyEquiv (S : Type u) (s : S) :
    HomotopyEquiv ((complexFunctor R).obj S) ((constantFunctor R).obj S) :=
  ((extraDegeneracy S s).map (ModuleCat.free R)).homotopyEquiv

instance augmentation_quasiIso (S : Type u) [Nonempty S] :
    QuasiIso ((augmentation R).app S) :=
  HomotopyEquiv.quasiIso_hom (NonemptyCechNerve.homotopyEquiv R S (Classical.choice ‹Nonempty S›))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra.NonemptyCechNerve
