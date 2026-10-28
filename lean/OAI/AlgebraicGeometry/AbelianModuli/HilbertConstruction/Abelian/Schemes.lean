import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Schemes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

noncomputable section

/-!
Concrete abelian-scheme infrastructure for HilbertConstruction. An abelian scheme is a
commutative group scheme that is proper and smooth with geometrically
connected fibers. Relative dimension is fixed. This file supplies no moduli
representability assumption and does not import the statement placeholder.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- An abelian scheme of relative dimension `g` over `S`. -/
structure AbelianScheme (g : ℕ) (S : Scheme.{u}) where
  scheme : Over S
  group : GrpObj scheme
  commutative : IsCommMonObj scheme
  proper : IsProper scheme.hom
  smoothDimension : SmoothOfRelativeDimension g scheme.hom
  connected : GeometricallyConnected scheme.hom

attribute [instance] AbelianScheme.group AbelianScheme.commutative
  AbelianScheme.proper AbelianScheme.smoothDimension AbelianScheme.connected

namespace AbelianScheme

variable {g : ℕ} {S T : Scheme.{u}}

instance (A : AbelianScheme g S) : Smooth A.scheme.hom :=
  SmoothOfRelativeDimension.smooth g A.scheme.hom

/-- Base change of an abelian scheme along any morphism of base schemes. -/
def pullback (A : AbelianScheme g S) (f : T ⟶ S) : AbelianScheme g T where
  scheme := (Over.pullback f).obj A.scheme
  group := Functor.grpObjObj
  commutative := inferInstance
  proper := inferInstanceAs (IsProper (Limits.pullback.snd A.scheme.hom f))
  smoothDimension := by
    have h := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact h.of_isPullback (IsPullback.of_hasPullback A.scheme.hom f) A.smoothDimension
  connected := inferInstanceAs
    (GeometricallyConnected (Limits.pullback.snd A.scheme.hom f))

/-- Points of an abelian scheme over a test scheme over its base. -/
abbrev Points (A : AbelianScheme g S) (T : Over S) := T ⟶ A.scheme

instance (A : AbelianScheme g S) (T : Over S) : CommGroup (A.Points T) :=
  CategoryTheory.Hom.commGroup

/-- Pullback of points is precomposition with the test-scheme morphism. -/
def pointsPullback (A : AbelianScheme g S) {T₁ T₂ : Over S} (f : T₁ ⟶ T₂) :
    A.Points T₂ →* A.Points T₁ :=
  ((yonedaGrpObj A.scheme).map f.op).hom

@[simp]
theorem pointsPullback_apply (A : AbelianScheme g S) {T₁ T₂ : Over S}
    (f : T₁ ⟶ T₂) (x : A.Points T₂) :
    A.pointsPullback f x = f ≫ x := rfl

/-- The subgroup of points killed by multiplication by `N`. -/
def torsionPoints (A : AbelianScheme g S) (N : ℕ) (T : Over S) :
    Subgroup (A.Points T) :=
  (powMonoidHom N).ker

@[simp]
theorem mem_torsionPoints (A : AbelianScheme g S) (N : ℕ) (T : Over S)
    (x : A.Points T) : x ∈ A.torsionPoints N T ↔ x ^ N = 1 := Iff.rfl

/-- Base change of torsion points. -/
def torsionPullback (A : AbelianScheme g S) (N : ℕ)
    {T₁ T₂ : Over S} (f : T₁ ⟶ T₂) :
    A.torsionPoints N T₂ →* A.torsionPoints N T₁ where
  toFun x := ⟨A.pointsPullback f x, by
    change (A.pointsPullback f x) ^ N = 1
    rw [← map_pow, (A.mem_torsionPoints N T₂ x).mp x.property, map_one]⟩
  map_one' := Subtype.ext (map_one (A.pointsPullback f))
  map_mul' x y := Subtype.ext (map_mul (A.pointsPullback f) x.val y.val)

/-- The group-valued functor of `N`-torsion points. -/
def torsionFunctor (A : AbelianScheme g S) (N : ℕ) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (A.torsionPoints N T.unop)
  map f := GrpCat.ofHom (A.torsionPullback N f.unop)
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.id_comp x.val
  map_comp f h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.assoc _ _ x.val

/-- Sections of the finite constant group scheme `(ℤ/Nℤ)^(2g)`.
Locally constant functions allow disconnected test schemes. -/
def constantLevelFunctor (g N : ℕ) (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of
    (LocallyConstant T.unop.left (Multiplicative (Fin (2 * g) → ZMod N)))
  map f := GrpCat.ofHom
    (LocallyConstant.comapMonoidHom ⟨f.unop.left, f.unop.left.continuous⟩)
  map_id T := by
    ext x t
    rfl
  map_comp f h := by
    ext x t
    rfl

/-- A full ordered level structure, expressed on all test schemes through
the functors of points of the constant group scheme and of `A[N]`. -/
def FullLevel (A : AbelianScheme g S) (N : ℕ) :=
  constantLevelFunctor g N S ≅ A.torsionFunctor N

end AbelianScheme

/-- The level-invertibility condition remains valid after arbitrary base change. -/
theorem level_unit_under_base_change {S T : Scheme.{u}} (f : T ⟶ S)
    (N : ℕ) (hN : IsUnit (N : Γ(S, ⊤))) : IsUnit (N : Γ(T, ⊤)) := by
  simpa using hN.map f.appTop.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
