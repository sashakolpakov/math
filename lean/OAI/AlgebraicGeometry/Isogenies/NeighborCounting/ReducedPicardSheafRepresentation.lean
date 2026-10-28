import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedGroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DualDataEquality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison

/-! # Reduced Picard Sheaf Representation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPicardSheafRepresentation

noncomputable section

/-! The supplied dual represents the commutative Picard sheaf over a reduced locally Noetherian base, with its original group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction

variable {S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] {g : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem givenDualPicardGroup_eq : Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D = D.abelian.group :=
  AbelianScheme.IsogenyQuotient.ReducedGroupRigidity.Construction.groupStructure_eq_of_origin_over_reduced_base D.abelian.scheme
    (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D) D.abelian.group (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup_commutative D)
    (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup_origin D)

def originalDualPicardHomEquiv (T : Over S) :
    (T ⟶ D.abelian.scheme) ≃* A.homogeneousPicardSheaf.obj.obj (.op T) where
  toEquiv := D.representable.homEquiv
  map_mul' x y := by
    have h : letI := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
        D.representable.homEquiv (x * y) = D.representable.homEquiv x * D.representable.homEquiv y := by
      let := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
      exact (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroupHomEquiv D T).map_mul x y
    have hm : let z := x * y
        letI := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
        x * y = z := by
      dsimp only
      rw [givenDualPicardGroup_eq D]
    exact (congrArg D.representable.homEquiv hm).symm.trans h

theorem originalDualPicardHomEquiv_apply (T : Over S) (x : T ⟶ D.abelian.scheme) :
    originalDualPicardHomEquiv D T x = D.representable.homEquiv x := rfl

def originalDualPicardSheafIso : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian.scheme) ≅
    AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb A := by
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents
    (fun T => (MulEquiv.ulift.trans (originalDualPicardHomEquiv D T.unop)).toCommGrpIso) ?_
  intro T U t
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  change D.representable.homEquiv (t.unop ≫ x) =
    Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A) t (D.representable.homEquiv x)
  exact (D.representable.homEquiv_comp t.unop x).trans
    (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A) t
      (D.representable.homEquiv x)).symm

theorem originalDualPicardSheafIso_apply (T : Over S) (x : T ⟶ D.abelian.scheme) :
    (originalDualPicardSheafIso D).hom.hom.app (.op T) (ULift.up x) =
      D.representable.homEquiv x := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPicardSheafRepresentation
