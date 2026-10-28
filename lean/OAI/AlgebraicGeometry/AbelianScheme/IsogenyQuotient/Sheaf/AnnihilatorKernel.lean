import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.AnnihilatorCharacter
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients

/-! # Annihilator Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
For a native subgroup inclusion, CartierDuality's canonical annihilator subobject
is exactly the kernel of restriction along that original inclusion.
The subobject's chosen representative introduces no new pairing map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem Sheaf.AnnihilatorKernel.Construction.sheafAnnihilator_mk_eq_kernel {S : Scheme.{u}} {G K H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (i : H ⟶ G) [Mono i] :
    CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e (Subobject.mk i) =
      kernelSubobject (e.rightAdjoint ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op) := by
  let j := Subobject.underlyingIso i
  have hj : (Subobject.mk i).arrow = j.hom ≫ i := (Subobject.underlyingIso_hom_comp_eq_mk i).symm
  have hm : e.rightAdjoint ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (Subobject.mk i).arrow.op =
      (e.rightAdjoint ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op) ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map j.hom.op := by
    rw [hj, op_comp, Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  exact (congrArg (fun f : K ⟶ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (Subobject.mk i : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) =>
    kernelSubobject f) hm).trans
      (kernelSubobject_comp_mono _ ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map j.hom.op))

def Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (i : H ⟶ G) [Mono i.hom.hom] :
    Subobject (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) := by
  haveI := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono i
  exact Subobject.mk (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)

theorem Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf_finiteLocallyFree {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (i : H ⟶ G) [Mono i.hom.hom]
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] :
    CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) := by
  have := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono i
  have hh : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) :=
    ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  exact hh.of_iso (Subobject.underlyingIso (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)).symm

variable {S : Scheme.{u}} {A B H : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj H] [IsCommMonObj H]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_annihilator_kernel (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom] :
    CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i) =
      kernelSubobject (e.toSheafPairing.rightAdjoint ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
          (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i).op) := by
  have := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono i
  exact Sheaf.AnnihilatorKernel.Construction.sheafAnnihilator_mk_eq_kernel e.toSheafPairing
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
