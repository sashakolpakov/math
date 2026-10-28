import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.PullbackIsoFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FrameAssociatedPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplicationPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PointSectionAvoidance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Regular Power Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On a Noetherian scheme, injective multiplication on a coherent sheaf is ensured by nonvanishing at a finite family of actual points. Over an infinite field an ample line bundle therefore has a positive power with a section acting injectively on that sheaf, including on nonreduced schemes and sheaves with embedded components. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsNoetherian X]

theorem Coherent.RegularPowerSection.coherent_exists_finite_section_regular_test
    (L : Line.Bundles.LineBundle X) (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (ι : Type u) (_ : Finite ι) (x : ι → X),
      ∀ s : Line.Bundles.structureModule X ⟶ L.sheaf,
        (∀ i, x i ∈ Ample.LineBundles.sectionNonvanishing s) → Mono (Module.SectionMultiplication.moduleSectionMultiply L M s) := by
  obtain ⟨k, U, ha, he, hcover⟩ := L.exists_finite_affine_frames
  have localTest (i : Fin k) :
      ∃ (ι : Type u) (_ : Finite ι) (x : ι → (U i).toScheme),
        ∀ s : Line.Bundles.structureModule (U i).toScheme ⟶ (L.pullback (U i).ι).sheaf,
          (∀ j, x j ∈ Ample.LineBundles.sectionNonvanishing s) →
            Mono (Module.SectionMultiplication.moduleSectionMultiply (L.pullback (U i).ι)
              ((Scheme.Modules.pullback (U i).ι).obj M) s) := by
    have : IsAffine (U i).toScheme := ha i
    have : IsNoetherianRing Γ((U i).toScheme, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U i).toScheme⟩
    have : ((Scheme.Modules.pullback (U i).ι).obj M).IsQuasicoherent :=
      Quasicoherent.PullbackIsoFiniteness.module_openPullback_quasicoherent (U i).ι M
    have : ((Scheme.Modules.pullback (U i).ι).obj M).IsFiniteType :=
      Quasicoherent.PullbackIsoFiniteness.module_openPullback_finiteType (U i).ι M
    exact Affine.FrameAssociatedPoints.affine_exists_finite_section_regular_test (L.pullback (U i).ι)
      ((Scheme.Modules.pullback (U i).ι).obj M) (he i).some
  choose J hJ x hx using localTest
  let (i : Fin k) : Finite (J i) := hJ i
  let y : (Σ i : Fin k, J i) → X := fun a => (U a.1).ι (x a.1 a.2)
  refine ⟨Σ i : Fin k, J i, inferInstance, y, fun s hs => ?_⟩
  apply Module.SectionMultiplicationPullback.moduleMap_mono_of_pullback_cover U hcover (Module.SectionMultiplication.moduleSectionMultiply L M s)
  intro i
  apply (Module.SectionMultiplicationPullback.moduleSectionMultiply_pullback_mono_iff (U i).ι L M s).mpr
  apply hx i (Ample.LineBundles.pullbackSection (U i).ι s)
  intro j
  rw [Section.Nonvanishing.sectionNonvanishing_pullback]
  exact hs ⟨i, j⟩

theorem Line.Bundles.LineBundle.IsAmple.exists_power_section_injective_on_coherent
    {K : Type u} [Field K] [Infinite K] (p : X ⟶ Spec (.of K))
    {L : Line.Bundles.LineBundle X} (hL : L.IsAmple)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (d : ℕ) (_ : 0 < d) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf),
      Mono (Module.SectionMultiplication.moduleSectionMultiply (L.tensorPower d) M s) := by
  obtain ⟨d, hd, _, t, ht, _⟩ := hL.projective_section_family
  obtain ⟨ι, hι, x, htest⟩ := Coherent.RegularPowerSection.coherent_exists_finite_section_regular_test (L.tensorPower d) M
  have : Finite ι := hι
  obtain ⟨s, hs⟩ := HilbertConstruction.Finite.PointSectionAvoidance.exists_section_nonvanishing_at_finite_points p (L.tensorPower d) x (by
    intro i
    obtain ⟨j, hj⟩ := ht (x i)
    exact ⟨t j, hj⟩)
  exact ⟨d, hd, s, htest s hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
