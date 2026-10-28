import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms

/-! # Group Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.GroupIso.FiniteGroupIso

noncomputable section

/-! An injective map of finite constant group functors of equal degree
is an isomorphism. The proof handles variation over disconnected bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Topology

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme.{0}} {G H : Type} [Group G] [Group H]
  (α : HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G ⟶ HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S H)

theorem label_injective
    (hinj : ∀ T : Over S, Function.Injective (α.app (.op T))) (s : S) :
    Function.Injective (HilbertConstruction.Constant.GroupMaps.constantGroupMapAt α s) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro c hc
  change c = 1
  let d : LocallyConstant S H := α.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (LocallyConstant.const S c)
  let U := ConstantSectionsOn.ConstantSections.fiberTest (ConstantSectionsOn.ConstantSections.baseTest S) d 1
  let j := ConstantSectionsOn.ConstantSections.fiberInclusion (ConstantSectionsOn.ConstantSections.baseTest S) d 1
  have hs : d s = 1 := hc
  let t : U.left := ⟨s, hs⟩
  have hn := ConcreteCategory.congr_hom (α.naturality j.op) (LocallyConstant.const S c)
  change α.app (.op U) (LocallyConstant.const U.left c) =
    d.comap ⟨j.left, j.left.continuous⟩ at hn
  have hd : d.comap ⟨j.left, j.left.continuous⟩ = 1 := by
    apply LocallyConstant.ext
    intro x
    exact x.property
  have hconst : LocallyConstant.const U.left c = 1 :=
    hinj U ((hn.trans hd).trans (map_one _).symm)
  exact congrArg (fun f : LocallyConstant U.left G => f t) hconst

def labelEquiv [Finite G] [Finite H]
    (hinj : ∀ T : Over S, Function.Injective (α.app (.op T)))
    (hcard : Nat.card G = Nat.card H) (s : S) : G ≃* H :=
  MulEquiv.ofBijective (HilbertConstruction.Constant.GroupMaps.constantGroupMapAt α s)
    ((label_injective α hinj s).bijective_of_nat_card_le hcard.ge)

def labelEquivs [Finite G] [Finite H]
    (hinj : ∀ T : Over S, Function.Injective (α.app (.op T)))
    (hcard : Nat.card G = Nat.card H) : LocallyConstant S (G ≃* H) where
  toFun := labelEquiv α hinj hcard
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    exact ((HilbertConstruction.Constant.GroupMaps.constantGroupMapLabels α).isLocallyConstant.eventually_eq s).mono
      (fun _ h => MulEquiv.ext (fun c => congrArg (fun f : G →* H => f c) h))

/-- Equal finite degree upgrades the injective natural map itself to an
isomorphism, with the inverse explicitly supplied by the label groups. -/
theorem isIso_of_injective_card_eq [Finite G] [Finite H]
    (hinj : ∀ T : Over S, Function.Injective (α.app (.op T)))
    (hcard : Nat.card G = Nat.card H) : IsIso α := by
  let e := HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels (labelEquivs α hinj hcard)
  have he : α = e.hom := by
    apply HilbertConstruction.Constant.GroupMaps.constantGroupMap_ext
    intro s
    apply MonoidHom.ext
    intro c
    rfl
  rw [he]
  exact e.isIso_hom

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.GroupIso.FiniteGroupIso
