import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor
import Mathlib.Algebra.Module.ZMod

/-! # Etale Label Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLabelTransport.Construction

noncomputable section

/-!
An actual isomorphism of the native active etale group schemes induces a
linear isomorphism of their F_q label planes and a bijection of all lines.
The linearity and line bijection are derived from the original group map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

/-- A locally constant section over the spectrum of a field is its
single value, with the original group operations. -/
def fieldConstantSectionsEquiv (k : Type u) [Field k] (G : Type u) [Group G] :
    LocallyConstant (Spec (.of k)) G ≃* G where
  toFun f := f (IsLocalRing.closedPoint k)
  invFun g := LocallyConstant.const _ g
  left_inv f := by
    apply LocallyConstant.ext
    intro x
    exact congrArg f (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The rational points of the actual finite etale model are its
original labels, rather than a separately assumed marking. -/
def fieldEtalePointsEquiv (k : Type u) [Field k] (G : Type u) [Group G] :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ (EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G).X) ≃* G :=
  (((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).app (op (Over.mk (𝟙 _)))).groupIsoToMulEquiv).trans
    (fieldConstantSectionsEquiv k G)

/-- Recover the label-group isomorphism from a native etale isomorphism. -/
def fieldEtaleLabelIso (k : Type u) [Field k] {G H : Type u} [Group G] [Group H]
    (a : EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G ≅ EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) H) : G ≃* H :=
  (fieldEtalePointsEquiv k G).symm.trans
    ((((yonedaGrp.mapIso a).app (op (Over.mk (𝟙 _)))).groupIsoToMulEquiv).trans
      (fieldEtalePointsEquiv k H))

/-- The recovered label map describes the original native map on
every test scheme, including disconnected and nonreduced tests. -/
theorem fieldEtaleLabelIso_sections (k : Type u) [Field k]
    {G H : Type u} [Group G] [Group H]
    (a : EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G ≅ EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) H)
    (T : Over (Spec (.of k))) (t : T ⟶ (EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G).X)
    (x : T.left) :
    LocallyConstant.toFun ((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) H).hom.app (op T)
      (t ≫ a.hom.hom.hom)) x =
      fieldEtaleLabelIso k a
        (LocallyConstant.toFun ((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).hom.app (op T) t) x) := by
  let α := (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).inv ≫ yonedaGrp.map a.hom ≫
    (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) H).hom
  have h : (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).hom ≫ α =
      yonedaGrp.map a.hom ≫ (EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) H).hom := by
    simp only [α, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have ht := congrArg (fun β => (β.app (op T)).hom t) h
  have hx := congrArg (fun c : LocallyConstant T.left H => c x) ht
  refine hx.symm.trans ((AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupMap_apply α T
    ((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) G).hom.app (op T) t) x).trans ?_)
  rw [show T.hom x = IsLocalRing.closedPoint k from Subsingleton.elim _ _]
  rfl

theorem fieldEtaleLabelIso_recovers (k : Type u) [Field k]
    {G H : Type u} [Group G] [Group H]
    (a : EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) G ≅ EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) H) :
    a.hom = EtaleSubgroups.Construction.etaleGroupMap (Spec (.of k)) (fieldEtaleLabelIso k a).toMonoidHom := by
  apply EtaleGroupFunctor.Construction.etaleGroupHom_ext
  intro T t x
  exact (fieldEtaleLabelIso_sections k a T t x).trans
    (EtaleSubgroups.Construction.etaleGroupMap_sections _ (fieldEtaleLabelIso k a).toMonoidHom T t x).symm

/-- Additive maps of F_q spaces are F_q-linear because q is prime. -/
def activeEtaleLinearEquiv (q : ℕ) [Fact q.Prime] (k : Type u) [Field k]
    (a : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q) :
    EtaleSubgroups.Construction.ActiveEtalePlane q ≃ₗ[ZMod q] EtaleSubgroups.Construction.ActiveEtalePlane q := by
  let big : ULift.{u} (Multiplicative (EtaleSubgroups.Construction.ActiveEtalePlane q)) ≃*
      ULift.{u} (Multiplicative (EtaleSubgroups.Construction.ActiveEtalePlane q)) := fieldEtaleLabelIso k a
  let small : Multiplicative (EtaleSubgroups.Construction.ActiveEtalePlane q) ≃* Multiplicative (EtaleSubgroups.Construction.ActiveEtalePlane q) :=
    MulEquiv.ulift.symm.trans big |>.trans MulEquiv.ulift
  let additive : EtaleSubgroups.Construction.ActiveEtalePlane q ≃+ EtaleSubgroups.Construction.ActiveEtalePlane q := AddEquiv.toMultiplicative.symm small
  exact LinearEquiv.ofBijective (additive.toAddMonoidHom.toZModLinearMap q) additive.bijective

/-- Every linear change of the actual active plane permutes all its
lines, with each source line and target line appearing once. -/
def activeEtaleLineEquiv (q : ℕ) [Fact q.Prime]
    (a : EtaleSubgroups.Construction.ActiveEtalePlane q ≃ₗ[ZMod q] EtaleSubgroups.Construction.ActiveEtalePlane q) :
    EtaleSubgroups.Construction.ActiveEtaleLine q ≃ EtaleSubgroups.Construction.ActiveEtaleLine q :=
  (Submodule.orderIsoMapComap a).toEquiv.subtypeEquiv (by
    intro L
    change Module.finrank (ZMod q) L = 1 ↔ Module.finrank (ZMod q) (L.map a.toLinearMap) = 1
    rw [a.finrank_map_eq L])

/-- The line permutation comes from the given native group-scheme
isomorphism, without a supplied choice bijection or linearity premise. -/
def nativeActiveEtaleLineEquiv (q : ℕ) [Fact q.Prime] (k : Type u) [Field k]
    (a : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q) :
    EtaleSubgroups.Construction.ActiveEtaleLine q ≃ EtaleSubgroups.Construction.ActiveEtaleLine q :=
  activeEtaleLineEquiv q (activeEtaleLinearEquiv q k a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLabelTransport.Construction
