import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! # Stable Graph Scheme -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.StableGraphScheme.Abelian.StableGraph

noncomputable section

/-!
The scheme of graphs invariant under separated diagonal actions.

For actions with eigenvalues `a t p` on the source and `b t q` on the
target, the graph of a matrix `L` is invariant exactly when
`b t q * L q p = L q p * a t p`. If every source-target pair of characters
is separated, these equations force `L = 0` over every coefficient algebra,
including algebras with nilpotents. The graph functor is then represented
by the actual base scheme, without a representability premise.

This is the local linear period problem, not the abelian moduli functor.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {K P Q T : Type u} [Field K]
  (a : T → P → K) (b : T → Q → K)

def Equations {R : Type u} [CommRing R] (k : K →+* R) (L : Matrix Q P R) : Prop :=
  ∀ t q p, k (b t q) * L q p = L q p * k (a t p)

/-- Direct invariance of the graph `(v, L v)` under the two diagonal actions. -/
def GraphInvariant [Fintype P] {R : Type u} [CommRing R]
    (k : K →+* R) (L : Matrix Q P R) : Prop :=
  ∀ t (v : P → R) q,
    k (b t q) * (∑ p, L q p * v p) =
      ∑ p, L q p * (k (a t p) * v p)

theorem graphInvariant_iff_equations [Fintype P] {R : Type u} [CommRing R]
    (k : K →+* R) (L : Matrix Q P R) :
    GraphInvariant a b k L ↔ Equations a b k L := by
  classical
  constructor
  · intro h t q p
    simpa [Pi.single_apply] using h t (Pi.single p 1) q
  · intro h t v q
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [← mul_assoc, h t q p, mul_assoc]

def Graph {R : Type u} [CommRing R] (k : K →+* R) :=
  {L : Matrix Q P R // Equations a b k L}

def zero {R : Type u} [CommRing R] (k : K →+* R) : Graph a b k :=
  ⟨0, fun _ _ _ => by simp⟩

/-- Separation in the base field forces every graph coordinate to vanish. -/
theorem matrix_eq_zero
    (hsep : ∀ q p, ∃ t, b t q ≠ a t p)
    {R : Type u} [CommRing R] (k : K →+* R) (L : Graph a b k) : L.val = 0 := by
  ext q p
  obtain ⟨t, ht⟩ := hsep q p
  have hu : IsUnit (k (b t q - a t p)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ht)).map k
  apply hu.mul_right_eq_zero.mp
  rw [map_sub, sub_mul, L.property t q p, mul_comm (L.val q p), sub_self]

theorem graph_subsingleton
    (hsep : ∀ q p, ∃ t, b t q ≠ a t p)
    {R : Type u} [CommRing R] (k : K →+* R) : Subsingleton (Graph a b k) :=
  ⟨fun L M => Subtype.ext ((matrix_eq_zero a b hsep k L).trans
    (matrix_eq_zero a b hsep k M).symm)⟩

def map {R R' : Type u} [CommRing R] [CommRing R']
    {k : K →+* R} {k' : K →+* R'} (f : R →+* R')
    (hf : ∀ c, f (k c) = k' c) (L : Graph a b k) : Graph a b k' :=
  ⟨fun q p => f (L.val q p), fun t q p => by
    have h := congrArg f (L.property t q p)
    simpa only [map_mul, hf] using h⟩

def coefficients (S : Over (Spec (CommRingCat.of K))) : K →+* Γ(S.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ S.hom.appTop).hom

theorem coefficients_naturality
    {S S' : Over (Spec (CommRingCat.of K))} (f : S' ⟶ S) (c : K) :
    f.left.appTop (coefficients S c) = coefficients S' c := by
  change f.left.appTop (S.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) = _
  change (f.left ≫ S.hom).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) = _
  rw [f.w]
  rfl

/-- The graph-parameter functor on all schemes over the coefficient field. -/
def functor : (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ Type u where
  obj S := Graph a b (coefficients S.unop)
  map f := TypeCat.ofHom (StableGraph.map a b f.unop.left.appTop.hom (coefficients_naturality f.unop))
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro L
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro L
    rfl

/-- The representing scheme is the coefficient-field base itself. -/
def scheme : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)

def pointEquiv (hsep : ∀ q p, ∃ t, b t q ≠ a t p)
    (S : Over (Spec (CommRingCat.of K))) :
    (S ⟶ scheme (K := K)) ≃ Graph a b (coefficients S) where
  toFun _ := zero a b (coefficients S)
  invFun _ := Over.homMk S.hom (Category.comp_id _)
  left_inv f := by
    apply Over.OverMorphism.ext
    change S.hom = f.left
    simpa [scheme] using f.w.symm
  right_inv L := Subtype.ext (matrix_eq_zero a b hsep (coefficients S) L).symm

/-- Actual representability, including all infinitesimal test schemes. -/
def representation (hsep : ∀ q p, ∃ t, b t q ≠ a t p) :
    (functor a b).RepresentableBy (scheme (K := K)) where
  homEquiv := pointEquiv a b hsep _
  homEquiv_comp {X X'} f g := by
    exact @Subsingleton.elim (Graph a b (coefficients X))
      (graph_subsingleton a b hsep _) _ _

theorem scheme_point_isolated (x : (scheme (K := K)).left) : IsOpen {x} := by
  have h : ({x} : Set (Spec (CommRingCat.of K))) = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun y => Set.mem_singleton_iff.mpr (Subsingleton.elim y x)
  change IsOpen ({x} : Set (Spec (CommRingCat.of K)))
  rw [h]
  exact isOpen_univ

end

end OAI.ArithmeticGeometry.Descent.CMVariety.StableGraphScheme.Abelian.StableGraph
