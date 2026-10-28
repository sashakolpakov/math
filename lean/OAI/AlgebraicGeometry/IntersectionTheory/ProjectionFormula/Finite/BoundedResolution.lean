import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BoundedResolution
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Projectives
import Mathlib.RingTheory.LocalRing.Module

/-! # Bounded Resolution -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.BoundedResolution

noncomputable section

/-! Finite modules of bounded projective dimension over Noetherian rings
have bounded resolutions by finite projectives. Over a local ring every
term of such a resolution is finite free. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

theorem exists_finite_bounded_resolution (M : ModuleCat.{u} R) [Module.Finite R M]
    (d : ℕ) [HasProjectiveDimensionLE M d] :
    ∃ P : ProjectiveResolution M, (∀ n, Module.Finite R (P.complex.X n)) ∧
      ∀ n, d < n → IsZero (P.complex.X n) := by
  induction d generalizing M with
  | zero =>
    let : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    refine ⟨ProjectiveResolution.self M, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact inferInstanceAs (Module.Finite R M)
      | succ n =>
        let : Subsingleton ((ProjectiveResolution.self M).complex.X (n + 1)) :=
          ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M (n + 1) (by omega))
        infer_instance
    · intro n hn
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
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
    let : HasProjectiveDimensionLE S.X₁ d :=
      (hS.hasProjectiveDimensionLT_X₃_iff d inferInstance).mp inferInstance
    obtain ⟨Q, hQfin, hQbound⟩ := ih S.X₁
    refine ⟨ResolutionAugment.resolution S hS Q, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact inferInstanceAs (Module.Finite R F)
      | succ n => exact hQfin n
    · intro n hn
      cases n with
      | zero => omega
      | succ n => exact hQbound n (by omega)

theorem exists_finite_free_bounded_resolution [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) [HasProjectiveDimensionLE M d] :
    ∃ P : ProjectiveResolution M,
      (∀ n, Module.Finite R (P.complex.X n) ∧ Module.Free R (P.complex.X n)) ∧
      ∀ n, d < n → IsZero (P.complex.X n) := by
  obtain ⟨P, hPfin, hPbound⟩ := exists_finite_bounded_resolution R M d
  refine ⟨P, ?_, hPbound⟩
  intro n
  let := hPfin n
  let : Module.Projective R (P.complex.X n) := ModuleCat.projective_of_module_projective _
  exact ⟨hPfin n, Module.free_of_flat_of_isLocalRing⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.BoundedResolution
