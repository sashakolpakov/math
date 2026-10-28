import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualGroup

/-! # Unbundled Dual Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroup

noncomputable section

/-! The Picard-derived dual group construction is independent of relative
dimension and agrees with the existing construction on bundled data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A : Over S} [GrpObj A] (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)

def dualPicardGroupRepresentable :
    ((UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupFunctor A ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy
      D.abelian :=
  D.representable.ofIso (UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupForgetIso A).symm

/-- This group law is constructed by representing tensor product and dualization. -/
@[instance_reducible]
def dualPicardGroup : GrpObj D.abelian :=
  GrpObj.ofRepresentableBy D.abelian
    (UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupFunctor A ⋙ forget₂ CommGrpCat GrpCat) (dualPicardGroupRepresentable D)

def dualPicardGroupHomEquiv (T : Over S) :
    letI := dualPicardGroup D
    (T ⟶ D.abelian) ≃* (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (op T) := by
  letI := dualPicardGroup D
  let a := dualPicardGroupRepresentable D
  refine { toEquiv := a.homEquiv', map_mul' := ?_ }
  intro x y
  change a.homEquiv' (lift x y ≫ a.homEquiv'.symm
      (a.homEquiv' (fst D.abelian D.abelian) *
        a.homEquiv' (snd D.abelian D.abelian))) = a.homEquiv' x * a.homEquiv' y
  simp only [a.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
  simp only [← a.homEquiv'_comp]
  simp

theorem dualPicardGroupHomEquiv_apply (T : Over S) (x : T ⟶ D.abelian) :
    dualPicardGroupHomEquiv D T x = D.representable.homEquiv x := rfl

theorem dualPicardGroup_commutative :
    letI := dualPicardGroup D
    IsCommMonObj D.abelian := by
  let := dualPicardGroup D
  apply (isCommMonObj_iff_isMulCommutative D.abelian).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (dualPicardGroupHomEquiv D T).injective
  rw [map_mul, map_mul, mul_comm]

theorem dualPicardGroup_origin :
    (dualPicardGroup D).toMonObj.one = D.group.toMonObj.one := by
  apply D.representable.homEquiv.injective
  have h : D.representable.homEquiv D.group.toMonObj.one =
      (UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A) (𝟙_ (Over S)) := by
    simpa only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using
      D.origin (𝟙_ (Over S))
  rw [h, UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one]
  exact (dualPicardGroupRepresentable D).homEquiv'.apply_symm_apply 1

theorem dualPicardGroup_ofBundled {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) :
    dualPicardGroup (UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) = CanonicalDualGroup.Construction.dualPicardGroup D := rfl

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroup
