import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Ordered Cech Zero Gluing -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechZeroGluing

noncomputable section

/-! Sheaf gluing identifies actual global sections with ordered Cech zero-cycles. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrderedCechZeroCoordinates

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

private theorem change_indices (s : OrderedCechEq.Construction.OrderedCechZeroCoordinates.cycles π M U) (V : X.Opens)
    {a b a' b' : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0} (ea : a = a') (eb : b = b')
    (ha : V ≤ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a) (hb : V ≤ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 b)
    (ha' : V ≤ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a') (hb' : V ≤ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 b')
    (h : M.presheaf.map (homOfLE ha).op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s a) =
      M.presheaf.map (homOfLE hb).op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s b)) :
    M.presheaf.map (homOfLE ha').op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s a') =
      M.presheaf.map (homOfLE hb').op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s b') := by
  subst a'
  subst b'
  exact h

theorem compatible_single (s : OrderedCechEq.Construction.OrderedCechZeroCoordinates.cycles π M U) (i j : ι) :
    M.presheaf.map (homOfLE (show OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) ⊓ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single j) ≤
      OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) from inf_le_left)).op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)) =
    M.presheaf.map (homOfLE (show OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) ⊓ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single j) ≤
      OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single j) from inf_le_right)).op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single j)) := by
  rcases lt_trichotomy i j with h | rfl | h
  · have hV : OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) ⊓ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single j) ≤
        OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 1 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair i j h) := by rw [OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair_open, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_open, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_open]
    have hc := OrderedCechEq.Construction.OrderedCechZeroCoordinates.compatible_on π M U s (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair i j h) _ hV
    exact change_indices π M U s _ (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair_delete_one i j h) (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair_delete_zero i j h)
      _ _ inf_le_left inf_le_right hc.symm
  · congr 2
  · have hV : OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) ⊓ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.single j) ≤
        OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 1 (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair j i h) := by rw [OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair_open, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_open, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_open, inf_comm]
    have hc := OrderedCechEq.Construction.OrderedCechZeroCoordinates.compatible_on π M U s (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair j i h) _ hV
    exact change_indices π M U s _ (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair_delete_zero j i h) (OrderedCechEq.Construction.OrderedCechZeroCoordinates.pair_delete_one j i h)
      _ _ inf_le_left inf_le_right hc

theorem compatible (s : OrderedCechEq.Construction.OrderedCechZeroCoordinates.cycles π M U) (a b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    M.presheaf.map (homOfLE (show OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a ⊓ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 b ≤
      OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a from inf_le_left)).op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s a) =
    M.presheaf.map (homOfLE (show OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a ⊓ OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 b ≤
      OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 b from inf_le_right)).op (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s b) := by
  obtain ⟨i, rfl⟩ : ∃ i, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i = a := ⟨a.1 0, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_of_index a⟩
  obtain ⟨j, rfl⟩ : ∃ j, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single j = b := ⟨b.1 0, OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_of_index b⟩
  exact compatible_single π M U s i j

omit π M in
theorem singleton_cover (hU : iSup U = ⊤) : (⊤ : X.Opens) ≤ iSup (OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0) := by
  intro x _
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i, by simpa only [OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_open] using hi⟩

private theorem product_ext {R : Type u} [Ring R] {J : Type u} (P : J → ModuleCat.{u} R)
    {x y : (∏ᶜ P : ModuleCat.{u} R)} (h : ∀ j, Pi.π P j x = Pi.π P j y) : x = y := by
  apply (ModuleCat.piIsoPi P).toLinearEquiv.injective
  funext j
  exact (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype P j) x).trans
    ((h j).trans (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype P j) y).symm)

theorem toCycles_bijective (hU : iSup U = ⊤) :
    Function.Bijective (OrderedCechSquare.Construction.OrderedCechAugmentation.toCycles π M U) := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · intro x y h
    apply F.eq_of_locally_eq' (OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0) ⊤ (fun a => (OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a).leTop)
      (singleton_cover U hU) x y
    intro a
    have hp := congrArg (fun z : OrderedCechEq.Construction.OrderedCechZeroCoordinates.cycles π M U => OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U z a) h
    exact (OrderedCechSquare.Construction.OrderedCechAugmentation.toCycles_π π M U x a).symm.trans
      (hp.trans (OrderedCechSquare.Construction.OrderedCechAugmentation.toCycles_π π M U y a))
  · intro s
    obtain ⟨z, hz, _⟩ := F.existsUnique_gluing' (OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0) ⊤
      (fun a => (OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a).leTop) (singleton_cover U hU)
      (OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U s) (compatible π M U s)
    refine ⟨z, Subtype.ext ?_⟩
    apply product_ext (fun a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a.1)
    intro a
    exact (OrderedCechSquare.Construction.OrderedCechAugmentation.toCycles_π π M U z a).trans (hz a)

def sectionsEquiv (hU : iSup U = ⊤) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) ≃ₗ[Γ(S, ⊤)] OrderedCechEq.Construction.OrderedCechZeroCoordinates.cycles π M U :=
  LinearEquiv.ofBijective (OrderedCechSquare.Construction.OrderedCechAugmentation.toCycles π M U) (toCycles_bijective π M U hU)

theorem sectionsEquiv_π (hU : iSup U = ⊤) (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤))
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    OrderedCechEq.Construction.OrderedCechZeroCoordinates.value π M U (sectionsEquiv π M U hU s) a =
      M.presheaf.map (OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a).leTop.op s :=
  OrderedCechSquare.Construction.OrderedCechAugmentation.toCycles_π π M U s a

end Construction.OrderedCechZeroCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechZeroGluing
