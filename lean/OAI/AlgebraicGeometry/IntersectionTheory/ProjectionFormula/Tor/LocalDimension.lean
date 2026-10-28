import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.LocalFree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Projectives

/-! # Local Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.LocalDimension

noncomputable section

/-! For finite modules over noetherian local rings, native Tor with the
residue field detects every finite projective-dimension bound. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem of_isZero (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ)
    (h : IsZero (((Tor (ModuleCat R) (d + 1)).obj M).obj
      (ModuleCat.of R (ResidueField R)))) : HasProjectiveDimensionLE M d := by
  induction d generalizing M with
  | zero =>
    let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    let : Module.Free R M := LocalFree.of_residue_second R M h
    let : Projective M := ModuleCat.projective_of_free (Module.Free.chooseBasis R M)
    exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance
  | succ d ih =>
    obtain ⟨F, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let π : ModuleCat.of R F ⟶ M := ModuleCat.ofHom f
    let : Epi π := (ModuleCat.epi_iff_surjective π).mpr hf
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel π)
        mono_f := inferInstanceAs (Mono (kernel.ι π))
        epi_g := inferInstanceAs (Epi π) }
    let : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of R F))
    let : Module.Finite R S.X₁ := Module.Finite.of_injective (kernel.ι π).hom
      ((ModuleCat.mono_iff_injective (kernel.ι π)).mp inferInstance)
    let e := FirstShift.shiftIso R (ModuleCat.of R (ResidueField R)) S hS d
    let : HasProjectiveDimensionLE S.X₁ d := ih S.X₁ (h.of_iso e.symm)
    exact (hS.hasProjectiveDimensionLT_X₃_iff d inferInstance).mpr inferInstance

theorem iff_isZero (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      IsZero (((Tor (ModuleCat R) (d + 1)).obj M).obj
        (ModuleCat.of R (ResidueField R))) := by
  constructor
  · intro h
    let := h
    exact (BoundedResolution.tor_isZero R (ModuleCat.of R (ResidueField R))
      M d (d + 1) (by omega)).of_iso
      (Symmetry.iso R M (ModuleCat.of R (ResidueField R)) (d + 1))
  · exact of_isZero R M d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.LocalDimension
