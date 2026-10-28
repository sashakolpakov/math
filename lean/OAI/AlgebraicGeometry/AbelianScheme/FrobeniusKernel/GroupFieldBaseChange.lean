import OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Group Field Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupFieldBaseChange.Construction

noncomputable section

/-! Scalar extension of FiniteEtale's actual finite commutative group schemes.
The new coordinate algebra is the tensor product, and its group law is
transported from the native scheme pullback, retaining nonreduced structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)

def finiteGroupFieldBaseMap : Spec (.of k') ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

def finiteGroupFieldBaseChangeSchemeIso :
    (Over.pullback (finiteGroupFieldBaseMap (k := k) (k' := k'))).obj G.scheme ≅
      GroupSchemes.FiniteEtale.affine k' (CommAlgCat.of k' (k' ⊗[k] G.algebra)) :=
  (pullbackSymmetry .. ≪≫ pullbackSpecIso' k k' G.algebra).asOver (Spec (.of k'))

@[instance_reducible]
def finiteGroupFieldBaseChangeGroup :
    CommGrpObj (GroupSchemes.FiniteEtale.affine k' (CommAlgCat.of k' (k' ⊗[k] G.algebra))) := by
  let F := Over.pullback (finiteGroupFieldBaseMap (k := k) (k' := k'))
  let e := finiteGroupFieldBaseChangeSchemeIso (k' := k') G
  let : GrpObj (F.obj G.scheme) := Functor.grpObjObj
  let : IsCommMonObj (F.obj G.scheme) := Functor.isCommMonObj_obj (F := F) (M := G.scheme)
  let : GrpObj (GroupSchemes.FiniteEtale.affine k' (CommAlgCat.of k' (k' ⊗[k] G.algebra))) := GrpObj.ofIso e
  have : IsMonHom e.hom := isMonHom_ofIso e
  have : IsCommMonObj (GroupSchemes.FiniteEtale.affine k' (CommAlgCat.of k' (k' ⊗[k] G.algebra))) := by
    apply (isCommMonObj_iff_isMulCommutative _).mpr
    intro T
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (cancel_mono e.inv).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact mul_comm _ _
  infer_instance

def finiteGroupFieldBaseChange : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k' where
  algebra := CommAlgCat.of k' (k' ⊗[k] G.algebra)
  finite := inferInstance
  group := finiteGroupFieldBaseChangeGroup G

theorem finiteGroupFieldBaseChange_finrank :
    Module.finrank k' (finiteGroupFieldBaseChange (k' := k') G).algebra =
      Module.finrank k G.algebra :=
  Module.finrank_baseChange

instance finiteGroupFieldBaseChangeSchemeIso_isMonHom :
    IsMonHom (show (Over.pullback (finiteGroupFieldBaseMap (k := k) (k' := k'))).obj G.scheme ⟶
      (finiteGroupFieldBaseChange (k' := k') G).scheme from
        (finiteGroupFieldBaseChangeSchemeIso (k' := k') G).hom) :=
  isMonHom_ofIso (finiteGroupFieldBaseChangeSchemeIso (k' := k') G)

def finiteGroupFieldBaseChangeGroupIso :
    (Over.pullback (finiteGroupFieldBaseMap (k := k) (k' := k'))).mapGrp.obj (Grp.mk G.scheme) ≅
      Grp.mk (finiteGroupFieldBaseChange (k' := k') G).scheme := by
  letI := finiteGroupFieldBaseChangeGroup (k' := k') G
  exact Grp.mkIso' (finiteGroupFieldBaseChangeSchemeIso (k' := k') G)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupFieldBaseChange.Construction
