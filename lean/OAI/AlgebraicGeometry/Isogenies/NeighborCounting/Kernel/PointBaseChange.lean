import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFlatKernelTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange

/-! # Point Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PointBaseChange

noncomputable section

/-! The actual point comparison commutes with kernel inclusions. This
turns integral point membership into membership in the base-changed
finite flat subgroup, without replacing its all-test model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

theorem pointPullbackGroupEquiv_comp {S T : Scheme.{u}} (f : T ⟶ S)
    {G H : Grp (Over S)} (c : G ⟶ H) (a : Over.mk f ⟶ G.X) :
    GroupPointBaseChange.pointPullbackGroupEquiv f H (a ≫ c.hom.hom) =
      GroupPointBaseChange.pointPullbackGroupEquiv f G a ≫ ((Over.pullback f).mapGrp.map c).hom.hom := by
  let e : (Over.map f).obj (Over.mk (𝟙 T)) ≅ Over.mk f :=
    Over.isoMk (Iso.refl _) (by simp)
  change (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f H (Over.mk (𝟙 T))) (e.hom ≫ (a ≫ c.hom.hom)) =
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G (Over.mk (𝟙 T))) (e.hom ≫ a) ≫
      ((Over.pullback f).mapGrp.map c).hom.hom
  rw [← Category.assoc]
  exact (Over.mapPullbackAdj f).homEquiv_naturality_right (e.hom ≫ a) c.hom.hom

theorem pullbackKernel_membership {S T : Scheme.{u}} {A : Over S} [GrpObj A]
    (K : Properties.FiniteFlatKernel A) (f : T ⟶ S) (a : Over.mk f ⟶ A) :
    (∃ b : Over.mk (𝟙 T) ⟶ (K.pullback f).carrier,
      b ≫ (K.pullback f).inclusion = GroupPointBaseChange.pointPullbackGroupEquiv f (Grp.mk A) a) ↔
    ∃ b : Over.mk f ⟶ K.carrier, b ≫ K.inclusion = a := by
  let c : Grp.mk K.carrier ⟶ Grp.mk A := Grp.homMk K.inclusion
  let eK := GroupPointBaseChange.pointPullbackGroupEquiv f (Grp.mk K.carrier)
  let eA := GroupPointBaseChange.pointPullbackGroupEquiv f (Grp.mk A)
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨eK.symm b, eA.injective ?_⟩
    have hn := pointPullbackGroupEquiv_comp f c (eK.symm b)
    exact hn.trans ((congrArg (fun z => z ≫ (Over.pullback f).map K.inclusion)
      (eK.apply_symm_apply b)).trans hb)
  · rintro ⟨b, hb⟩
    refine ⟨eK b, ?_⟩
    exact (pointPullbackGroupEquiv_comp f c b).symm.trans (congrArg eA hb)

theorem mapIsoKernel_membership {S : Scheme.{u}} {A B U : Over S} [GrpObj A] [GrpObj B]
    (K : Properties.FiniteFlatKernel A) (e : A ≅ B) [IsMonHom e.hom] (a : U ⟶ B) :
    (∃ b : U ⟶ (K.mapIso e).carrier, b ≫ (K.mapIso e).inclusion = a) ↔
      ∃ b : U ⟶ K.carrier, b ≫ K.inclusion = a ≫ e.inv := by
  constructor
  · rintro ⟨b, hb⟩
    let b' : U ⟶ K.carrier := b
    change b' ≫ (K.inclusion ≫ e.hom) = a at hb
    refine ⟨b', ?_⟩
    exact (cancel_mono e.hom).mp (by
      simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hb)
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    change b ≫ (K.inclusion ≫ e.hom) = a
    rw [← Category.assoc, hb, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem baseChangedPointEquiv_pullback {S₁ S₂ S₀ : Scheme.{u}} (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)
    (G : Grp (Over S₁)) (H : Grp (Over S₂))
    (e : (Over.pullback f).mapGrp.obj G ≅ (Over.pullback g).mapGrp.obj H)
    (a : Over.mk f ⟶ G.X) :
    GroupPointBaseChange.pointPullbackGroupEquiv g H (GroupPointBaseChange.baseChangedPointEquiv f g G H e a) =
      GroupPointBaseChange.pointPullbackGroupEquiv f G a ≫ e.hom.hom.hom := by
  exact (GroupPointBaseChange.pointPullbackGroupEquiv g H).apply_symm_apply _

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PointBaseChange
