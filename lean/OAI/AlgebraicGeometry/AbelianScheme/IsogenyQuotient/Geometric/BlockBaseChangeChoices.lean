import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.BlockChoices

/-! # Block Base Change Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.BlockBaseChangeChoices.Construction

noncomputable section

/-! Geometric subgroup choices before and after actual base change
are equivalent. The comparison retains their native included points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def testIsoPointsMulEquiv {S : Scheme.{0}} {X Y : Over S} (e : X ≅ Y)
    (G : Over S) [GrpObj G] : (X ⟶ G) ≃* (Y ⟶ G) where
  toFun x := e.inv ≫ x
  invFun y := e.hom ≫ y
  left_inv x := by simp only [e.hom_inv_id_assoc]
  right_inv y := by simp only [e.inv_hom_id_assoc]
  map_mul' x y := MonObj.comp_mul _ _ _

def geometricParameterIdentityIso {S S' : Scheme.{0}} (b : S' ⟶ S) :
    (Over.map b).obj (Over.mk (𝟙 S')) ≅ Over.mk b := Over.isoMk (Iso.refl _) rfl

def nativeBlockGeometricBaseChangePointsEquiv
    {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ) (b : S' ⟶ S) :
    (Over.mk (𝟙 S') ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) ≃*
      (Over.mk b ⟶ OppositeKernel.Construction.torsionBlock n p) :=
  (Intrinsic.BlockBaseChangePoints.Construction.nativeBlockBaseChangePointsEquiv A p n b (Over.mk (𝟙 S'))).trans
    (testIsoPointsMulEquiv (geometricParameterIdentityIso b) (OppositeKernel.Construction.torsionBlock n p))

theorem typedMultiplicativeSubgroupEquiv_membership
    {G H M : Type*} [Group G] [Group H] [Group M] (e : G ≃* H)
    (J : {F : Subgroup G // Nonempty (F ≃* M)}) (x : G) :
    e x ∈ (BlockChoices.Construction.typedMultiplicativeSubgroupEquiv e J).val ↔ x ∈ J.val := by
  change e x ∈ J.val.map e.toMonoidHom ↔ x ∈ J.val
  constructor
  · rintro ⟨y, hy, he⟩
    exact e.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

def typedSubgroupTransport {X Y G H M : Type*} [Group G] [Group H] [Group M]
    (L : X ≃ {F : Subgroup G // Nonempty (F ≃* M)})
    (R : Y ≃ {F : Subgroup H // Nonempty (F ≃* M)}) (e : G ≃* H) : X ≃ Y :=
  (L.trans (BlockChoices.Construction.typedMultiplicativeSubgroupEquiv e)).trans R.symm

theorem typedSubgroupTransport_membership {X Y G H M : Type*} [Group G] [Group H] [Group M]
    (L : X ≃ {F : Subgroup G // Nonempty (F ≃* M)})
    (R : Y ≃ {F : Subgroup H // Nonempty (F ≃* M)}) (e : G ≃* H) (F : X) (x : G) :
    e x ∈ (R (typedSubgroupTransport L R e F)).val ↔ x ∈ (L F).val := by
  change e x ∈ (R (R.symm (BlockChoices.Construction.typedMultiplicativeSubgroupEquiv e (L F)))).val ↔ _
  rw [R.apply_symm_apply]
  exact typedMultiplicativeSubgroupEquiv_membership e (L F) x

theorem typedSubgroupTransport_predicate {X Y G H M : Type*} [Group G] [Group H] [Group M]
    (L : X ≃ {F : Subgroup G // Nonempty (F ≃* M)})
    (R : Y ≃ {F : Subgroup H // Nonempty (F ≃* M)}) (e : G ≃* H)
    (PL : X → G → Prop) (PR : Y → H → Prop)
    (hL : ∀ F x, x ∈ (L F).val ↔ PL F x)
    (hR : ∀ F y, y ∈ (R F).val ↔ PR F y) (F : X) (x : G) :
    PR (typedSubgroupTransport L R e F) (e x) ↔ PL F x :=
  (hR _ _).symm.trans ((typedSubgroupTransport_membership L R e F x).trans (hL F x))

def typedSubgroupTransportData {X Y G H M : Type*} [Group G] [Group H] [Group M]
    (L : X ≃ {F : Subgroup G // Nonempty (F ≃* M)})
    (R : Y ≃ {F : Subgroup H // Nonempty (F ≃* M)}) (e : G ≃* H)
    (PL : X → G → Prop) (PR : Y → H → Prop)
    (hL : ∀ F x, x ∈ (L F).val ↔ PL F x)
    (hR : ∀ F y, y ∈ (R F).val ↔ PR F y) :
    {c : X ≃ Y // ∀ F x, PR (c F) (e x) ↔ PL F x} :=
  ⟨typedSubgroupTransport L R e, typedSubgroupTransport_predicate L R e PL PR hL hR⟩

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ)
  (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  [IsFinite (OppositeKernel.Construction.torsionBlock n p).hom] [Etale (OppositeKernel.Construction.torsionBlock n p).hom]
  [IsFinite (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom]
  [Etale (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom]

def geometricSupportedBaseChangeData :
    {c : SubgroupFunctor.Construction.SupportedChoice ((Over.pullback b).obj A.scheme) n M ((Over.pullback b).map p)
        (Over.mk (𝟙 (Spec (.of k)))) ≃ SubgroupFunctor.Construction.SupportedChoice A.scheme n M p (Over.mk b) //
      ∀ F x, nativeBlockGeometricBaseChangePointsEquiv A p n b x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈
          (c F).val.subgroup.points (Over.mk b) (𝟙 _) ↔
        x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p) ∈
          F.val.subgroup.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _)} :=
  typedSubgroupTransportData
    (BlockChoices.Construction.geometricSupportedChoiceEquiv n M k (𝟙 (Spec (.of k))) ((Over.pullback b).map p))
    (BlockChoices.Construction.geometricSupportedChoiceEquiv n M k b p)
    (nativeBlockGeometricBaseChangePointsEquiv A p n b)
    (fun F x => x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p) ∈
      F.val.subgroup.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _))
    (fun F x => x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈ F.val.subgroup.points (Over.mk b) (𝟙 _))
    (BlockChoices.Construction.geometricSupportedChoiceEquiv_membership n M k (𝟙 (Spec (.of k))) ((Over.pullback b).map p))
    (BlockChoices.Construction.geometricSupportedChoiceEquiv_membership n M k b p)

def geometricSupportedBaseChangeEquiv :
    SubgroupFunctor.Construction.SupportedChoice ((Over.pullback b).obj A.scheme) n M ((Over.pullback b).map p) (Over.mk (𝟙 (Spec (.of k)))) ≃
      SubgroupFunctor.Construction.SupportedChoice A.scheme n M p (Over.mk b) :=
  (geometricSupportedBaseChangeData A p n M k b).val

theorem geometricSupportedBaseChangeEquiv_membership
    (F : SubgroupFunctor.Construction.SupportedChoice ((Over.pullback b).obj A.scheme) n M ((Over.pullback b).map p) (Over.mk (𝟙 (Spec (.of k)))))
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    nativeBlockGeometricBaseChangePointsEquiv A p n b x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈
        (geometricSupportedBaseChangeEquiv A p n M k b F).val.subgroup.points (Over.mk b) (𝟙 _) ↔
      x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p) ∈ F.val.subgroup.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _) :=
  (geometricSupportedBaseChangeData A p n M k b).property F x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.BlockBaseChangeChoices.Construction
