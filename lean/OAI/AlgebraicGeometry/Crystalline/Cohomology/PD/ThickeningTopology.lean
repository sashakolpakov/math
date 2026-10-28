import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-! # Thickening Topology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.ThickeningTopology.PDThickeningTopology

noncomputable section

/-!
# Units and topology of actual PD thickenings

The defining ideal is elementwise nilpotent. Reduction therefore reflects
units and induces a homeomorphism of prime spectra, without a uniform
nilpotence bound on the entire ideal.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra k A] (T : Thickening.AffinePDThickening p k A)

theorem isUnit_of_reduction (x : T.ring) (hx : IsUnit (T.reduction x)) : IsUnit x := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨y, hy⟩ := T.reduction_surjective (↑(v⁻¹) : A)
  have hk : x * y - 1 ∈ RingHom.ker T.reduction := by
    change T.reduction (x * y - 1) = 0
    simp [map_sub, map_mul, ← hv, hy]
  have hu := (T.kernel_element_isNilpotent (x * y - 1) hk).isUnit_add_one
  have hxy : IsUnit (x * y) := by simpa only [sub_add_cancel] using hu
  exact isUnit_of_mul_isUnit_left hxy

theorem isUnit_reduction_iff (x : T.ring) : IsUnit (T.reduction x) ↔ IsUnit x :=
  ⟨isUnit_of_reduction p k A T x, fun h => h.map T.reduction⟩

theorem reduction_isHomeomorph : IsHomeomorph (PrimeSpectrum.comap T.reduction) := by
  apply PrimeSpectrum.isHomeomorph_comap T.reduction
  · intro x
    obtain ⟨y, hy⟩ := T.reduction_surjective x
    exact ⟨1, by decide, ⟨y, by simpa only [pow_one] using hy⟩⟩
  · intro x hx
    exact mem_nilradical.mpr (T.kernel_element_isNilpotent x hx)

theorem homeomorph_of_comp_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : Y → Z) (g : X → Y) (hg : IsHomeomorph g)
    (hfg : IsHomeomorph (f ∘ g)) : IsHomeomorph f := by
  let e := IsHomeomorph.homeomorph g hg
  have he : f = (f ∘ g) ∘ e.symm := by
    funext y
    change f y = f (e (e.symm y))
    rw [e.apply_symm_apply]
  exact he.symm ▸ hfg.comp e.symm.isHomeomorph

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.ThickeningTopology.PDThickeningTopology
