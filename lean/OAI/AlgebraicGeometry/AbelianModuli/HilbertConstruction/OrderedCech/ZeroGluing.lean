import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZeroCoordinates
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Zero Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZeroGluing.OrderedCechZeroCoordinates

noncomputable section

/-! Sheaf gluing identifies actual global sections with ordered Cech zero-cycles. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

private theorem change_indices (s : ZeroCoordinates.OrderedCechZeroCoordinates.cycles c M U) (V : X.Opens)
    {a b a' b' : Ordered.SectionCechIndices.OrderedCechIndex ι 0} (ea : a = a') (eb : b = b')
    (ha : V ≤ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a) (hb : V ≤ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 b)
    (ha' : V ≤ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a') (hb' : V ≤ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 b')
    (h : M.presheaf.map (homOfLE ha).op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s a) =
      M.presheaf.map (homOfLE hb).op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s b)) :
    M.presheaf.map (homOfLE ha').op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s a') =
      M.presheaf.map (homOfLE hb').op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s b') := by
  subst a'
  subst b'
  exact h

theorem compatible_single (s : ZeroCoordinates.OrderedCechZeroCoordinates.cycles c M U) (i j : ι) :
    M.presheaf.map (homOfLE (show ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single i) ⊓ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single j) ≤
      ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single i) from inf_le_left)).op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s (ZeroCoordinates.OrderedCechZeroCoordinates.single i)) =
    M.presheaf.map (homOfLE (show ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single i) ⊓ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single j) ≤
      ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single j) from inf_le_right)).op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s (ZeroCoordinates.OrderedCechZeroCoordinates.single j)) := by
  rcases lt_trichotomy i j with h | rfl | h
  · have hV : ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single i) ⊓ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single j) ≤
        ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 1 (ZeroCoordinates.OrderedCechZeroCoordinates.pair i j h) := by rw [ZeroCoordinates.OrderedCechZeroCoordinates.pair_open, ZeroCoordinates.OrderedCechZeroCoordinates.single_open, ZeroCoordinates.OrderedCechZeroCoordinates.single_open]
    have hc := ZeroCoordinates.OrderedCechZeroCoordinates.compatible_on c M U s (ZeroCoordinates.OrderedCechZeroCoordinates.pair i j h) _ hV
    exact change_indices c M U s _ (ZeroCoordinates.OrderedCechZeroCoordinates.pair_delete_one i j h) (ZeroCoordinates.OrderedCechZeroCoordinates.pair_delete_zero i j h)
      _ _ inf_le_left inf_le_right hc.symm
  · congr 2
  · have hV : ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single i) ⊓ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 (ZeroCoordinates.OrderedCechZeroCoordinates.single j) ≤
        ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 1 (ZeroCoordinates.OrderedCechZeroCoordinates.pair j i h) := by rw [ZeroCoordinates.OrderedCechZeroCoordinates.pair_open, ZeroCoordinates.OrderedCechZeroCoordinates.single_open, ZeroCoordinates.OrderedCechZeroCoordinates.single_open, inf_comm]
    have hc := ZeroCoordinates.OrderedCechZeroCoordinates.compatible_on c M U s (ZeroCoordinates.OrderedCechZeroCoordinates.pair j i h) _ hV
    exact change_indices c M U s _ (ZeroCoordinates.OrderedCechZeroCoordinates.pair_delete_zero j i h) (ZeroCoordinates.OrderedCechZeroCoordinates.pair_delete_one j i h)
      _ _ inf_le_left inf_le_right hc

theorem compatible (s : ZeroCoordinates.OrderedCechZeroCoordinates.cycles c M U) (a b : Ordered.SectionCechIndices.OrderedCechIndex ι 0) :
    M.presheaf.map (homOfLE (show ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a ⊓ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 b ≤
      ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a from inf_le_left)).op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s a) =
    M.presheaf.map (homOfLE (show ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a ⊓ ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 b ≤
      ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 b from inf_le_right)).op (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s b) := by
  obtain ⟨i, rfl⟩ : ∃ i, ZeroCoordinates.OrderedCechZeroCoordinates.single i = a := ⟨a.1 0, ZeroCoordinates.OrderedCechZeroCoordinates.single_of_index a⟩
  obtain ⟨j, rfl⟩ : ∃ j, ZeroCoordinates.OrderedCechZeroCoordinates.single j = b := ⟨b.1 0, ZeroCoordinates.OrderedCechZeroCoordinates.single_of_index b⟩
  exact compatible_single c M U s i j

omit c M in
theorem singleton_cover (hU : iSup U = ⊤) : (⊤ : X.Opens) ≤ iSup (ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0) := by
  intro x _
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ZeroCoordinates.OrderedCechZeroCoordinates.single i, by simpa only [ZeroCoordinates.OrderedCechZeroCoordinates.single_open] using hi⟩

private theorem product_ext {R : Type u} [Ring R] {J : Type u} (P : J → ModuleCat.{u} R)
    {x y : (∏ᶜ P : ModuleCat.{u} R)} (h : ∀ j, Pi.π P j x = Pi.π P j y) : x = y := by
  apply (ModuleCat.piIsoPi P).toLinearEquiv.injective
  funext j
  exact (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype P j) x).trans
    ((h j).trans (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype P j) y).symm)

theorem toCycles_bijective (hU : iSup U = ⊤) :
    Function.Bijective (Augmentation.orderedCechSectionToCycles c M U) := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · intro x y h
    apply F.eq_of_locally_eq' (ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0) ⊤ (fun a => (ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a).leTop)
      (singleton_cover U hU) x y
    intro a
    have hp := congrArg (fun z : ZeroCoordinates.OrderedCechZeroCoordinates.cycles c M U => ZeroCoordinates.OrderedCechZeroCoordinates.value c M U z a) h
    exact (SectionCycleValues.orderedCechSectionToCycles_π c M U x a).symm.trans
      (hp.trans (SectionCycleValues.orderedCechSectionToCycles_π c M U y a))
  · intro s
    obtain ⟨z, hz, _⟩ := F.existsUnique_gluing' (ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0) ⊤
      (fun a => (ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a).leTop) (singleton_cover U hU)
      (ZeroCoordinates.OrderedCechZeroCoordinates.value c M U s) (compatible c M U s)
    refine ⟨z, Subtype.ext ?_⟩
    apply product_ext (fun a : Ordered.SectionCechIndices.OrderedCechIndex ι 0 => Ordered.CoefficientCechTerms.coefficientCechFactor c M U 0 a.1)
    intro a
    exact (SectionCycleValues.orderedCechSectionToCycles_π c M U z a).trans (hz a)

def sectionsEquiv (hU : iSup U = ⊤) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤) ≃ₗ[R] ZeroCoordinates.OrderedCechZeroCoordinates.cycles c M U :=
  LinearEquiv.ofBijective (Augmentation.orderedCechSectionToCycles c M U) (toCycles_bijective c M U hU)

theorem sectionsEquiv_π (hU : iSup U = ⊤) (s : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤))
    (a : Ordered.SectionCechIndices.OrderedCechIndex ι 0) :
    ZeroCoordinates.OrderedCechZeroCoordinates.value c M U (sectionsEquiv c M U hU s) a =
      M.presheaf.map (ZeroCoordinates.OrderedCechZeroCoordinates.intersection U 0 a).leTop.op s :=
  SectionCycleValues.orderedCechSectionToCycles_π c M U s a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZeroGluing.OrderedCechZeroCoordinates
