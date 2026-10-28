import OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedSupportFiltration
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

/-! # Support Filtration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.SupportFiltration

noncomputable section

/-!
# ChernClass: support-filtration vanishing on every ambient open

Restrict the actual closed filtration to an arbitrary open subset. The two
orders of taking that open subset and a layer complement are homeomorphic
as pairs. The existing relative-cochain triple sequence then transfers layer
vanishing to the restricted total support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedSupportFiltration.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- An actual homeomorphism of pairs induces an isomorphism of relative cochains. -/
def pairHomeomorphCochainIso {R : Type} [Ring R] (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : ∀ x, x ∈ A ↔ e x ∈ B) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y B ≅ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (TopCat.isoOfHomeo e).hom (fun x hx => (he x).mp hx)
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (TopCat.isoOfHomeo e).inv
    (fun y hy => (he (e.symm y)).mpr (by simpa using hy))
  hom_inv_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id M (TopCat.isoOfHomeo e).inv
    (TopCat.isoOfHomeo e).hom (fun y hy => (he (e.symm y)).mpr (by simpa using hy))
    (fun x hx => (he x).mp hx) (TopCat.isoOfHomeo e).inv_hom_id
  inv_hom_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id M (TopCat.isoOfHomeo e).hom
    (TopCat.isoOfHomeo e).inv (fun x hx => (he x).mp hx)
    (fun y hy => (he (e.symm y)).mpr (by simpa using hy)) (TopCat.isoOfHomeo e).hom_inv_id

/-- The resulting isomorphism is induced by those genuine pair maps. -/
def pairHomeomorphCohomologyIso {R : Type} [Ring R] (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y B n ≅ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n :=
  HomologicalComplex.homologyMapIso (pairHomeomorphCochainIso M e A B he) n

variable (X : TopCat.{0}) (U : Opens X)

/-- Restrict a closed support to the actual open subspace. -/
def restrictClosedSupport (F : Closeds X) : Closeds U :=
  ⟨{x | x.val ∈ F}, F.isClosed.preimage continuous_subtype_val⟩

/-- The part of the ambient open contained in the complement of the earlier support. -/
def layerOpen (F : Closeds X) : Opens (TopCat.of ((F : Set X)ᶜ : Set X)) :=
  ⟨{x | x.val ∈ U}, U.isOpen.preimage continuous_subtype_val⟩

/-- Taking an open restriction and a complement in either order gives the same actual pair. -/
def openLayerSwap (F : Closeds X) :
    TopCat.of ((restrictClosedSupport X U F : Set U)ᶜ : Set U) ≃ₜ TopCat.of (layerOpen X U F) where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- Layer support is preserved under the actual exchange of subspaces. -/
theorem openLayerSwap_mem (F G : Closeds X)
    (x : TopCat.of ((restrictClosedSupport X U F : Set U)ᶜ : Set U)) :
    x ∈ (CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of U) (restrictClosedSupport X U F) (restrictClosedSupport X U G))ᶜ ↔
      openLayerSwap X U F x ∈ {y : layerOpen X U F | y.val ∈ CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer X F G}ᶜ := Iff.rfl

/-- Vanishing on all opens of every actual layer implies vanishing on the
chosen open restriction of the whole finite support. -/
theorem closedSupportFiltration_open_isZero {R : Type} [Ring R] (M : ModuleCat.{0} R)
    (N : ℕ) (F : Fin (N + 1) → Closeds X) (hF : Monotone F) (hfirst : F 0 = ⊥) (n : ℕ)
    (hLayer : ∀ i : Fin N, ∀ V : Opens (TopCat.of ((F i.castSucc : Set X)ᶜ : Set X)),
      IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V)
        {x : V | x.val ∈ CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer X (F i.castSucc) (F i.succ)}ᶜ n)) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U)
      {x : U | x.val ∈ (F (Fin.last N) : Set X)}ᶜ n) := by
  apply CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportFiltration_isZero M (TopCat.of U) N (fun i => restrictClosedSupport X U (F i))
    (fun i j hij x hx => hF hij hx) n
  · have he : restrictClosedSupport X U (F 0) = ⊥ := by
      rw [hfirst]
      rfl
    simpa only [he, Closeds.coe_bot] using CycleClass.Geometric.ClosedSupportFiltration.Cycles.cohomologyWithEmptySupport_isZero M (TopCat.of U) n
  · intro i
    let e := pairHomeomorphCohomologyIso M (openLayerSwap X U (F i.castSucc))
      (CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of U) (restrictClosedSupport X U (F i.castSucc))
        (restrictClosedSupport X U (F i.succ)))ᶜ
      {x : layerOpen X U (F i.castSucc) | x.val ∈ CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer X (F i.castSucc) (F i.succ)}ᶜ
      (openLayerSwap_mem X U (F i.castSucc) (F i.succ)) n
    exact (hLayer i (layerOpen X U (F i.castSucc))).of_iso e.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.SupportFiltration
