import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Characters
import Mathlib.Algebra.Module.ZMod

/-! # Group Product Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates

noncomputable section

/-! The ordinary product coordinates are additive, hence ZMod-linear
on q-torsion points. The same coordinates are used by the graph and
mixed-kernel enumeration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {T A M E : Over S} [GrpObj A] [GrpObj M] [GrpObj E]

/-- Postcomposition by the actual group-scheme isomorphism. -/
def groupPointIso (e : A ≅ M) [IsMonHom e.hom] : (T ⟶ A) ≃* (T ⟶ M) where
  toFun a := a ≫ e.hom
  invFun a := a ≫ e.inv
  left_inv a := by simp
  right_inv a := by simp
  map_mul' a b := MonObj.mul_comp a b e.hom

def groupSchemePointIso {G H : Grp (Over S)} (e : G ≅ H) :
    (T ⟶ G.X) ≃* (T ⟶ H.X) := by
  let eraw : G.X ≅ H.X := (Grp.forget _).mapIso e
  have : IsMonHom eraw.hom := e.hom.hom.isMonHom_hom
  exact groupPointIso eraw

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
  (m : (T ⟶ M) ≃* Multiplicative F) (v : (T ⟶ E) ≃* Multiplicative V)

def productPointAddEquiv : Additive (T ⟶ M ⊗ E) ≃+ V × F where
  toEquiv := Additive.toMul.trans
    (GenericParameters.blockCoordinates (m.toEquiv.trans Multiplicative.toAdd) (v.toEquiv.trans Multiplicative.toAdd))
  map_add' a b := by
    change ((v ((a.toMul * b.toMul) ≫ snd M E)).toAdd,
      (m ((a.toMul * b.toMul) ≫ fst M E)).toAdd) = _
    simp only [MonObj.mul_comp, map_mul]
    rfl

def sourceProductPointAddEquiv (e : M ⊗ E ≅ A) [IsMonHom e.hom] :
    Additive (T ⟶ A) ≃+ V × F := by
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact (groupPointIso (T := T) e.symm).toAdditive.trans (productPointAddEquiv m v)

variable (q : ℕ) [IsCommMonObj A] [Module (ZMod q) (Additive (T ⟶ A))]
  (mq : (T ⟶ M) ≃* Multiplicative (ZMod q))
  {W : Type} [AddCommGroup W] [Module (ZMod q) W]
  (vq : (T ⟶ E) ≃* Multiplicative W)

/-- Additive coordinates on q-torsion preserve the unique ZMod action. -/
def sourceProductPointLinearEquiv [Fact q.Prime] (e : M ⊗ E ≅ A) [IsMonHom e.hom] :
    Additive (T ⟶ A) ≃ₗ[ZMod q] W × ZMod q :=
  LinearEquiv.ofBijective ((sourceProductPointAddEquiv mq vq e).toAddMonoidHom.toZModLinearMap q)
    (sourceProductPointAddEquiv mq vq e).bijective

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates
