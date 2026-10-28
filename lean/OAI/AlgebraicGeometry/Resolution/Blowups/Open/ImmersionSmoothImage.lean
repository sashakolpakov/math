import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.IdealSheafBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.IntegralOpenCover

/-! # Immersion Smooth Image -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Open.ImmersionSmoothImage.Construction

noncomputable section

/-! The scheme image of an open immersion into a smooth complex scheme is smooth. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem openImmersion_kernel_dichotomy {V X : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] [IsIntegral X] : j.ker = ⊥ ∨ j.ker = ⊤ := by
  by_cases hv : Nonempty V
  · let : Nonempty V := hv
    let : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j)⟩
    let : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
    exact Or.inl j.ker_eq_bot
  · let : IsEmpty V := not_nonempty_iff.mp hv
    exact Or.inr (Scheme.ker_eq_top_of_isEmpty j)

theorem openImmersion_image_smooth_of_integral_open_cover
    {V X B : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (f : X ⟶ B)
    {ι : Type v} (C : ι → Scheme.{u}) (a : ∀ t, C t ⟶ X)
    [∀ t, IsOpenImmersion (a t)] [∀ t, IsIntegral (C t)] [∀ t, Smooth (a t ≫ f)]
    (hcover : ⨆ t, (a t).opensRange = ⊤) : Smooth (j.imageι ≫ f) := by
  apply Global.PointedSmoothCenter.Construction.idealSheaf_subscheme_smooth_of_open_charts j.ker f C a hcover
  intro t
  have hk := IdealSheafBaseChange.Construction.kernel_comap_of_open_pullback j (pullback.fst (a t) j) (pullback.snd (a t) j)
    (a t) (IsPullback.of_hasPullback (a t) j)
  rw [hk]
  rcases openImmersion_kernel_dichotomy (pullback.fst (a t) j) with hz | ht
  · rw [hz]
    infer_instance
  · rw [ht]
    infer_instance

theorem smooth_complex_pointed_integral_chart {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (x : X) :
    ∃ (C : Scheme) (a : C ⟶ X), IsOpenImmersion a ∧ IsIntegral C ∧
      Smooth (a ≫ f) ∧ ∃ q : C, a q = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let A : X.affineOpens := ⟨U, hU⟩
  let : Algebra ℂ Γ(X, A) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f A
  let : Algebra.Smooth ℂ Γ(X, A) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f A
  let : IsOpenImmersion A.2.fromSpec := A.2.isOpenImmersion_fromSpec
  have hx : x ∈ A.2.fromSpec.opensRange := by
    rw [A.2.opensRange_fromSpec]
    exact hxU
  obtain ⟨p, hp⟩ := hx
  obtain ⟨C, q, hq⟩ := Blowups.Smooth.IntegralOpenCover.Construction.smooth_integral_open_chart_at ℂ p
  change PrimeSpectrum.comap C.map.toRingHom q = p at hq
  let a := Spec.map (CommRingCat.ofHom C.map.toRingHom) ≫ A.2.fromSpec
  refine ⟨Spec C.carrier, a, inferInstance, inferInstance, inferInstance, q, ?_⟩
  change A.2.fromSpec (PrimeSpectrum.comap C.map.toRingHom q) = x
  rw [hq]
  exact hp

theorem openImmersion_image_smooth_complex {V X : Scheme}
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] : Smooth (j.imageι ≫ f) := by
  classical
  choose C a ha hC hs q hq using smooth_complex_pointed_integral_chart f
  let : ∀ x, IsOpenImmersion (a x) := ha
  let : ∀ x, IsIntegral (C x) := hC
  let : ∀ x, Smooth (a x ≫ f) := hs
  apply openImmersion_image_smooth_of_integral_open_cover j f C a
  apply top_le_iff.mp
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, q x, hq x⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Open.ImmersionSmoothImage.Construction
