import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FieldBaseChangeMaps
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange

/-! # Group Field Point Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupFieldPointTransport.Construction

noncomputable section

/-! The scalar-extended finite groups retain their original points on
every base-changed test scheme. The comparison preserves the actual
tower transition maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup

theorem schemePoint_comp_square {S : Scheme.{u}} {U G H J K : Over S}
    (x : U ⟶ G) (e : G ⟶ H) (b : H ⟶ K) (a : G ⟶ J) (f : J ⟶ K) (h : e ≫ b = a ≫ f) :
    (x ≫ a) ≫ f = (x ≫ e) ≫ b :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => x ≫ z) h.symm).trans (Category.assoc _ _ _).symm)

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
variable (U : Over (Spec (.of k')))

def finiteGroupFieldPointEquiv :
    ((Over.map (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).obj U ⟶ G.scheme) ≃*
      (U ⟶ (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).scheme) :=
  (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))
    (Grp.mk G.scheme) U).trans
      (((yonedaGrp.mapIso (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') G)).app (op U)).groupIsoToMulEquiv)

theorem finiteGroupFieldPointEquiv_apply
    (x : (Over.map (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).obj U ⟶ G.scheme) :
    finiteGroupFieldPointEquiv G U x =
      (Over.mapPullbackAdj (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).homEquiv U G.scheme x ≫
        (FieldBaseChangeMaps.Construction.finiteGroupNativeBaseChangeIso (k' := k') G).hom := rfl

variable {G} {H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k}
variable (a : G.scheme ⟶ H.scheme) [IsMonHom a]

omit [IsMonHom a] in
theorem finiteGroupFieldPointEquiv_postcomp
    (x : (Over.map (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).obj U ⟶ G.scheme) :
    finiteGroupFieldPointEquiv H U (x ≫ a) =
      finiteGroupFieldPointEquiv G U x ≫ FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap (k' := k') a := by
  rw [finiteGroupFieldPointEquiv_apply, finiteGroupFieldPointEquiv_apply]
  exact (congrArg (fun y => y ≫ (FieldBaseChangeMaps.Construction.finiteGroupNativeBaseChangeIso (k' := k') H).hom)
    ((Over.mapPullbackAdj (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).homEquiv_naturality_right x a)).trans
      (schemePoint_comp_square _ _ _ _ _ (FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap_square (k' := k') a))

omit [IsMonHom a] in
theorem finiteGroupFieldPointEquiv_symm_postcomp
    (x : U ⟶ (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).scheme) :
    (finiteGroupFieldPointEquiv H U).symm
        (x ≫ FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap (k' := k') a) =
      (finiteGroupFieldPointEquiv G U).symm x ≫ a := by
  apply (finiteGroupFieldPointEquiv H U).injective
  rw [MulEquiv.apply_symm_apply, finiteGroupFieldPointEquiv_postcomp, MulEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupFieldPointTransport.Construction
