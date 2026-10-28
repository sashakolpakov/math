import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterSourceMap
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceCharacters

/-! # Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChange.Construction

noncomputable section

/-! The canonical comparison between a parameter pullback of a changed
base and its original one-step pullback retains group laws and kernels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme} (s : S' ⟶ S) (Q : Over S')

def parameterBaseChangeTestIso (U : Over Q.left) :
    (Over.map s).obj ((Over.map Q.hom).obj U) ≅
      (Over.map ((Over.map s).obj Q).hom).obj U :=
  Over.isoMk (Iso.refl U.left) (by
    change (𝟙 U.left) ≫ (U.hom ≫ Q.hom ≫ s) = (U.hom ≫ Q.hom) ≫ s
    rw [Category.id_comp, Category.assoc])

def parameterBaseChangeInv (A : Over S) :
    (Over.pullback Q.hom).obj ((Over.pullback s).obj A) ⟶
      (Over.pullback ((Over.map s).obj Q).hom).obj A :=
  (Over.pullbackComp Q.hom s).inv.app A

theorem parameterBaseChangeInv_isMonHom (G : Grp (Over S)) :
    IsMonHom (parameterBaseChangeInv s Q G.X) := by
  let a := (GroupPullbackComposition.Construction.groupPullbackCompIso Q.hom s).inv.app G
  have h : a.hom.hom = parameterBaseChangeInv s Q G.X :=
    GroupPullbackComposition.Construction.groupPullbackCompIso_inv Q.hom s G
  have ha : IsMonHom a.hom.hom := inferInstance
  exact (congrArg (fun t : (Over.pullback Q.hom).obj ((Over.pullback s).obj G.X) ⟶
    (Over.pullback ((Over.map s).obj Q).hom).obj G.X => IsMonHom t) h).mp ha

theorem parameterBaseChangeInv_projection (A : Over S) :
    (parameterBaseChangeInv s Q A).left ≫ pullback.fst A.hom (Q.hom ≫ s) =
      pullback.fst (pullback.snd A.hom s) Q.hom ≫ pullback.fst A.hom s := by
  let e := (Over.forget Q.left).mapIso ((Over.pullbackComp Q.hom s).app A)
  exact (congrArg (fun t => e.inv ≫ t)
    (CartierDuality.SliceCharacters.Construction.Schemes.pullbackComp_hom_fst Q.hom s A).symm).trans
      (e.inv_hom_id_assoc _)

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
theorem parameterBaseChangeSquare :
    parameterBaseChangeInv s Q A ≫ (Over.pullback ((Over.map s).obj Q).hom).map f =
      (Over.pullback Q.hom).map ((Over.pullback s).map f) ≫ parameterBaseChangeInv s Q B :=
  ((Over.pullbackComp Q.hom s).inv.naturality f).symm

def parameterBaseChangeKernelMap :
    Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((Over.pullback s).map f)) ⟶
      Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback ((Over.map s).obj Q).hom).map f) := by
  have : IsMonHom (parameterBaseChangeInv s Q A) := parameterBaseChangeInv_isMonHom s Q (Grp.mk A)
  have : IsMonHom (parameterBaseChangeInv s Q B) := parameterBaseChangeInv_isMonHom s Q (Grp.mk B)
  exact CharacterSourceMap.Construction.kernelSourceSquareMap
    ((Over.pullback ((Over.map s).obj Q).hom).map f)
    ((Over.pullback Q.hom).map ((Over.pullback s).map f))
    (parameterBaseChangeInv s Q A) (parameterBaseChangeInv s Q B)
    (parameterBaseChangeSquare s Q f)

omit [IsMonHom f] in
theorem parameterBaseChangeKernelMap_inclusion :
    parameterBaseChangeKernelMap s Q f ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback ((Over.map s).obj Q).hom).map f) =
      Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback Q.hom).map ((Over.pullback s).map f)) ≫
        parameterBaseChangeInv s Q A := by
  have : IsMonHom (parameterBaseChangeInv s Q A) := parameterBaseChangeInv_isMonHom s Q (Grp.mk A)
  have : IsMonHom (parameterBaseChangeInv s Q B) := parameterBaseChangeInv_isMonHom s Q (Grp.mk B)
  exact CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion
    ((Over.pullback ((Over.map s).obj Q).hom).map f)
    ((Over.pullback Q.hom).map ((Over.pullback s).map f))
    (parameterBaseChangeInv s Q A) (parameterBaseChangeInv s Q B)
    (parameterBaseChangeSquare s Q f)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChange.Construction
