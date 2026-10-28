import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor
import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousPowers
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Canonical Dual Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualGroup

noncomputable section

/-! The dual group law derived from the actual homogeneous Picard group functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def dualPicardGroupRepresentable :
    ((GroupFunctor.Construction.homogeneousPicardGroupFunctor A ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy
      D.abelian.scheme :=
  D.representable.ofIso (GroupFunctor.Construction.homogeneousPicardGroupForgetIso A).symm

/-- This group law is constructed by representing tensor product and dualization. -/
@[instance_reducible]
def dualPicardGroup : GrpObj D.abelian.scheme :=
  GrpObj.ofRepresentableBy D.abelian.scheme
    (GroupFunctor.Construction.homogeneousPicardGroupFunctor A ⋙ forget₂ CommGrpCat GrpCat) (dualPicardGroupRepresentable D)

def dualPicardGroupHomEquiv (T : Over S) :
    letI := dualPicardGroup D
    (T ⟶ D.abelian.scheme) ≃* A.homogeneousPicardSheaf.obj.obj (op T) := by
  letI := dualPicardGroup D
  let a := dualPicardGroupRepresentable D
  refine { toEquiv := a.homEquiv', map_mul' := ?_ }
  intro x y
  change a.homEquiv' (lift x y ≫ a.homEquiv'.symm
      (a.homEquiv' (fst D.abelian.scheme D.abelian.scheme) *
        a.homEquiv' (snd D.abelian.scheme D.abelian.scheme))) = a.homEquiv' x * a.homEquiv' y
  simp only [a.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
  simp only [← a.homEquiv'_comp]
  simp

theorem dualPicardGroupHomEquiv_apply (T : Over S) (x : T ⟶ D.abelian.scheme) :
    dualPicardGroupHomEquiv D T x = D.representable.homEquiv x := rfl

theorem dualPicardGroup_commutative :
    letI := dualPicardGroup D
    IsCommMonObj D.abelian.scheme := by
  let := dualPicardGroup D
  apply (isCommMonObj_iff_isMulCommutative D.abelian.scheme).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (dualPicardGroupHomEquiv D T).injective
  rw [map_mul, map_mul, mul_comm]

/-- The Picard-derived group law equips the representing scheme with an abelian-scheme structure. -/
def picardDualAbelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S where
  scheme := D.abelian.scheme
  group := dualPicardGroup D
  commutative := dualPicardGroup_commutative D
  proper := D.abelian.proper
  smoothDimension := D.abelian.smoothDimension
  connected := D.abelian.connected

theorem dualPicardGroup_origin :
    (dualPicardGroup D).toMonObj.one = D.abelian.group.toMonObj.one := by
  apply D.representable.homEquiv.injective
  have h : D.representable.homEquiv D.abelian.group.toMonObj.one =
      A.trivialHomogeneousPicardClass (𝟙_ (Over S)) := by
    simpa only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using
      D.origin (𝟙_ (Over S))
  rw [h, HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one]
  exact (dualPicardGroupRepresentable D).homEquiv'.apply_symm_apply 1

theorem dualPicardTensorPower_eq_groupPow
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) :
    letI := dualPicardGroup D
    HomogeneousTensorPower.Construction.dualPicardTensorPower p hp hS D = (𝟙 D.abelian.scheme) ^ p := by
  let := dualPicardGroup D
  apply (dualPicardGroupHomEquiv D D.abelian.scheme).injective
  rw [map_pow, dualPicardGroupHomEquiv_apply, dualPicardGroupHomEquiv_apply]
  change D.representable.homEquiv
      (D.representable.homEquiv.symm
        ((HomogeneousTensorPower.Construction.homogeneousPicardTensorPower p hp hS A).hom.app (op D.abelian.scheme)
          (D.representable.homEquiv (𝟙 D.abelian.scheme)))) = _
  rw [Equiv.apply_symm_apply]
  exact HomogeneousPowers.Construction.homogeneousPicardTensorPower_eq_pow p hp hS A D.abelian.scheme _

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualGroup
