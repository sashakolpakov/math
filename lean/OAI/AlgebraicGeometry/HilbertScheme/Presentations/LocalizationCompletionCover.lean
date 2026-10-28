import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProductModules
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization

/-! # Localization Completion Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationCompletionCover

noncomputable section

/-! Localization away from one element and completion along that element
together give a faithfully flat affine cover of a Noetherian base. -/

universe u v

theorem faithfullyFlat_of_residue_lifts (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Flat R A]
    (h : ∀ (m : Ideal R), m.IsMaximal → ∃ φ : A →+* R ⧸ m,
      ∀ r : R, φ (algebraMap R A r) = Ideal.Quotient.mk m r) :
    Module.FaithfullyFlat R A := by
  refine ⟨fun m hm => ?_⟩
  let : m.IsMaximal := hm
  obtain ⟨φ, hφ⟩ := h m hm
  have hker : m.map (algebraMap R A) ≤ RingHom.ker φ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change φ (algebraMap R A r) = 0
    rw [hφ]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [Ideal.smul_top_eq_map]
  intro htop
  have hmem : (1 : A) ∈ m.map (algebraMap R A) := by
    have hz : (1 : A) ∈ (⊤ : Submodule R A) := Submodule.mem_top
    rw [← htop] at hz
    exact hz
  have hz : φ 1 = 0 := hker hmem
  exact one_ne_zero (by simpa only [map_one] using hz)

theorem localization_completion_faithfullyFlat (R : Type u) [CommRing R]
    [IsNoetherianRing R] (s : R) :
    Module.FaithfullyFlat R
      (Localization.Away s × AdicCompletion (Ideal.span {s}) R) := by
  let L := Localization.Away s
  let I : Ideal R := Ideal.span {s}
  let H := AdicCompletion I R
  let : Module.Flat R L := IsLocalization.flat L (Submonoid.powers s)
  let : Module.Flat R (L × H) := Presentations.Flat.ProductModules.flat_product_modules R L H
  apply faithfullyFlat_of_residue_lifts
  intro m hm
  let : m.IsMaximal := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  by_cases hs : s ∈ m
  · have hI : I ≤ m := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hs)
    let ψ : H →+* R ⧸ m :=
      (Ideal.Quotient.factor hI).comp (AdicCompletion.evalOneₐ I).toRingHom
    refine ⟨ψ.comp (RingHom.snd L H), fun _ => ?_⟩
    rfl
  · have hu : IsUnit (algebraMap R (R ⧸ m) s) := by
      apply isUnit_iff_ne_zero.mpr
      exact fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    let ψ : L →+* R ⧸ m := IsLocalization.Away.lift s hu
    refine ⟨ψ.comp (RingHom.fst L H), fun r => ?_⟩
    change ψ (algebraMap R L r) = Ideal.Quotient.mk m r
    exact IsLocalization.Away.lift_eq s hu r

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationCompletionCover
