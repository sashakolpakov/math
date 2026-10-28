import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierIntrinsicRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Cartier
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels

/-! # Cartier Sheaf Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
The native opposite kernel is the kernel in commutative fppf sheaves.
The comparison uses literal character restriction on every test scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Native monomorphisms remain monomorphisms of the represented
commutative fppf sheaves. -/
theorem CartierSheafKernels.Construction.representedFppfAbMap_mono {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) [Mono f.hom.hom] :
    Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) := by
  constructor
  intro F a b h
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  have he := congrArg (fun z => z.hom.app T x) h
  have he' : (a.hom.app T x).down ≫ f.hom.hom =
      (b.hom.app T x).down ≫ f.hom.hom := congrArg ULift.down he
  exact congrArg ULift.up ((cancel_mono f.hom.hom).mp he')

variable {R : CommRingCat.{u}} {G H : Grp (Over (Spec R))}
variable (P : CartierModel.Construction.CartierCoordinates R G) (Q : CartierModel.Construction.CartierCoordinates R H) (i : H ⟶ G)

/-- Character restriction is the actual sheaf Cartier-dual map. -/
theorem CartierModel.Construction.CartierCoordinates.representedCartierDualIso_restriction [IsCommMonObj G.X] [IsCommMonObj H.X] :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (P.restriction Q i) ≫ Q.representedCartierDualIso.hom =
      P.representedCartierDualIso.hom ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec R)).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i).op := by
  apply CartierDuality.SheafEvaluation.Construction.Schemes.sheafDualHom_ext
  intro T d x
  let d' : T ⟶ P.dualGroup.X := d.down
  let x' : T ⟶ H.X := x.down
  exact (Q.representedCartierDualIso_value T (d' ≫ (P.restriction Q i).hom.hom) x').trans
    ((congrArg (fun χ : CharacterGroups.Construction.CharacterSections H T =>
      ULift.up (χ.app (op (Over.mk (𝟙 T))) x'))
        (P.restriction_on_characters Q i T d')).trans
      (P.representedCartierDualIso_value T d' (x' ≫ i.hom.hom)).symm)

def CartierModel.Construction.CartierCoordinates.representedRestriction : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) P.dualGroup ⟶
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) Q.dualGroup := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (P.restriction Q i)

def CartierModel.Construction.CartierCoordinates.representedAnnihilatorInclusion : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) (P.annihilatorGroup Q i) ⟶
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) P.dualGroup := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (P.annihilatorInclusion Q i)

instance CartierModel.Construction.CartierCoordinates.representedAnnihilatorInclusion_mono : Mono (P.representedAnnihilatorInclusion Q i) :=
  CartierSheafKernels.Construction.representedFppfAbMap_mono _

theorem CartierModel.Construction.CartierCoordinates.representedAnnihilator_condition :
    P.representedAnnihilatorInclusion Q i ≫ P.representedRestriction Q i = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  change ULift.up ((x ≫ (P.annihilatorInclusion Q i).hom.hom) ≫
    (P.restriction Q i).hom.hom) = ULift.up 1
  apply congrArg ULift.up
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => x ≫ f) (P.annihilatorInclusion_restriction Q i)).trans (MonObj.comp_one x))

/-- All sections of the categorical sheaf kernel factor uniquely
through the original native opposite-kernel group scheme. -/
def CartierModel.Construction.CartierCoordinates.representedAnnihilatorIsLimit :
    IsLimit (KernelFork.ofι (P.representedAnnihilatorInclusion Q i)
      (P.representedAnnihilator_condition Q i)) := by
  apply CartierDuality.SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints
  intro T x hx
  obtain ⟨x⟩ := x
  have hx' : x ≫ (P.restriction Q i).hom.hom = 1 := congrArg ULift.down hx
  obtain ⟨y, hy, _⟩ := (P.annihilator_universal Q i T x).mp
    ((P.annihilator_condition Q i T x).mp hx')
  exact ⟨ULift.up y, congrArg ULift.up hy⟩

/-- The native opposite kernel and the sheaf kernel are the same
embedded subgroup, not merely isomorphic abstract groups. -/
theorem CartierModel.Construction.CartierCoordinates.representedAnnihilator_subobject :
    Subobject.mk (P.representedAnnihilatorInclusion Q i) =
      kernelSubobject (P.representedRestriction Q i) := by
  let e := (P.representedAnnihilatorIsLimit Q i).conePointUniqueUpToIso
    (kernelIsKernel (P.representedRestriction Q i))
  apply Subobject.mk_eq_mk_of_comm _ _ e
  exact IsLimit.conePointUniqueUpToIso_hom_comp (P.representedAnnihilatorIsLimit Q i)
    (kernelIsKernel _) WalkingParallelPair.zero

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
