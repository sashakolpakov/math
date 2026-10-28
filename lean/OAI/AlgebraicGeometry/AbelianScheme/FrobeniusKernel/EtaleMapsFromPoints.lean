import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLabelTransport

/-! # Etale Maps From Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleMapsFromPoints.Construction

noncomputable section

/-!
For the actual constant etale models over a field, a native map is
determined on all test schemes by its rational-point map. Bijectivity
on those points therefore constructs a native group-scheme inverse.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable (k : Type u) [Field k] {G H : Type u} [Group G] [Group H]
variable (a : EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G ⟶ EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) H)

def fieldEtaleLabelMap : G →* H :=
  (EtaleLabelTransport.Construction.fieldEtalePointsEquiv k H).toMonoidHom.comp
    (((yonedaGrp.map a).app (op (Over.mk (𝟙 _)))).hom.comp
      (EtaleLabelTransport.Construction.fieldEtalePointsEquiv k G).symm.toMonoidHom)

theorem fieldEtaleLabelMap_sections (T : Over (Spec (.of k)))
    (t : T ⟶ (EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G).X) (x : T.left) :
    LocallyConstant.toFun ((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) H).hom.app (op T)
      (t ≫ a.hom.hom)) x =
      fieldEtaleLabelMap k a
        (LocallyConstant.toFun ((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).hom.app (op T) t) x) := by
  let α := (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).inv ≫ yonedaGrp.map a ≫
    (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) H).hom
  have h : (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).hom ≫ α =
      yonedaGrp.map a ≫ (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) H).hom := by
    simp only [α, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have ht := congrArg (fun β => (β.app (op T)).hom t) h
  have hx := congrArg (fun c : LocallyConstant T.left H => c x) ht
  refine hx.symm.trans ((AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupMap_apply α T
    ((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).hom.app (op T) t) x).trans ?_)
  rw [show T.hom x = IsLocalRing.closedPoint k from Subsingleton.elim _ _]
  rfl

theorem fieldEtaleLabelMap_recovers :
    a = EtaleSubgroups.Construction.etaleGroupMap (Spec (.of k)) (fieldEtaleLabelMap k a) := by
  apply EtaleGroupFunctor.Construction.etaleGroupHom_ext
  intro T t x
  exact (fieldEtaleLabelMap_sections k a T t x).trans
    (EtaleSubgroups.Construction.etaleGroupMap_sections _ (fieldEtaleLabelMap k a) T t x).symm

/-- The inverse is constructed from labels and checked as an inverse
of the original native map, rather than just its rational-point map. -/
def fieldEtaleIsoOfPoints
    (ha : Function.Bijective ((yonedaGrp.map a).app (op (Over.mk (𝟙 _))))) :
    EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G ≅ EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) H :=
  EtaleGroupFunctor.Construction.etaleGroupIso (Spec (.of k)) (MulEquiv.ofBijective (fieldEtaleLabelMap k a)
    ((EtaleLabelTransport.Construction.fieldEtalePointsEquiv k H).bijective.comp
      (ha.comp (EtaleLabelTransport.Construction.fieldEtalePointsEquiv k G).symm.bijective)))

theorem fieldEtaleIsoOfPoints_hom
    (ha : Function.Bijective ((yonedaGrp.map a).app (op (Over.mk (𝟙 _))))) :
    (fieldEtaleIsoOfPoints k a ha).hom = a :=
  (fieldEtaleLabelMap_recovers k a).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleMapsFromPoints.Construction
