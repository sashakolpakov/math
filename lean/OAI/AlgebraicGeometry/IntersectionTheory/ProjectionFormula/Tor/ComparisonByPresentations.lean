import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.AcyclicShift
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Comparison By Presentations -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.ComparisonByPresentations

noncomputable section

/-! An exact functor that sends finite free presentations to Tor-acyclic
presentations computes the same native Tor objects, provided the degree-zero
tensor functors agree naturally. The proof shifts the degree through actual
finite free presentations; no derived comparison is assumed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [IsNoetherianRing R]
  (N : ModuleCat.{u} R) (N' : ModuleCat.{u} S)
  (H : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [H.Additive] [H.PreservesHomology]
  (G : ModuleCat.{u} S ⥤ ModuleCat.{u} R) [G.Additive] [PreservesFiniteLimits G]
  (e : H ⋙ tensorRight N' ⋙ G ≅ tensorRight N)
  (hfree : ∀ (P : ModuleCat.{u} R) [Module.Free R P] [Module.Finite R P] (i : ℕ),
    IsZero (((Tor (ModuleCat S) (i + 1)).obj (H.obj P)).obj N'))

include e hfree

theorem exists_iso (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M] :
    Nonempty (G.obj (((Tor (ModuleCat S) n).obj (H.obj M)).obj N') ≅
      (((Tor (ModuleCat R) n).obj M).obj N)) := by
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    cases n with
    | zero =>
      exact ⟨G.mapIso (Flat.torZeroIso S (H.obj M) N') ≪≫ e.app M ≪≫
        (Flat.torZeroIso R M N).symm⟩
    | succ n =>
      obtain ⟨F, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
      let π : ModuleCat.of R F ⟶ M := ModuleCat.ofHom f
      let : Epi π := (ModuleCat.epi_iff_surjective π).mpr hf
      let T := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      have hT : T.ShortExact :=
        { exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel π)
          mono_f := inferInstanceAs (Mono (kernel.ι π))
          epi_g := inferInstanceAs (Epi π) }
      let : Projective T.X₂ := inferInstanceAs (Projective (ModuleCat.of R F))
      let : Module.Finite R T.X₁ := Module.Finite.of_injective (kernel.ι π).hom
        ((ModuleCat.mono_iff_injective (kernel.ι π)).mp inferInstance)
      let : Mono T.f := hT.mono_f
      let : Epi T.g := hT.epi_g
      have hHT := hT.map H
      cases n with
      | zero =>
        let g := (tensorRight N').map (H.map T.f)
        let g₀ := (tensorRight N).map T.f
        let : HasKernel g := HasLimit.mk ⟨_, ModuleCat.kernelIsLimit g⟩
        let : HasKernel g₀ := HasLimit.mk ⟨_, ModuleCat.kernelIsLimit g₀⟩
        let : HasKernel (G.map g) := HasLimit.mk ⟨_, ModuleCat.kernelIsLimit (G.map g)⟩
        let ek : G.obj (.of S g.hom.ker) ≅ .of R g₀.hom.ker :=
          G.mapIso (ModuleCat.kernelIsoKer g).symm ≪≫ PreservesKernel.iso G g ≪≫
            kernel.mapIso (G.map g) g₀ (e.app T.X₁) (e.app T.X₂) (e.hom.naturality T.f) ≪≫
              ModuleCat.kernelIsoKer g₀
        exact ⟨G.mapIso (AcyclicShift.kernelIso S N' (T.map H) hHT
          (hfree (.of R F) 0)) ≪≫ ek ≪≫ (OneFirst.kernelIso R N T hT).symm⟩
      | succ n =>
        obtain ⟨ei⟩ := ih (n + 1) (by omega) T.X₁
        exact ⟨G.mapIso (AcyclicShift.shiftIso S N' (T.map H) hHT n
          (hfree (.of R F) (n + 1)) (hfree (.of R F) n)) ≪≫ ei ≪≫
            (FirstShift.shiftIso R N T hT n).symm⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.ComparisonByPresentations
