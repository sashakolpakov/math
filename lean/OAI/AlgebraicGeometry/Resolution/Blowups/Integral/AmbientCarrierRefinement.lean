import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents

/-! # Ambient Carrier Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.AmbientCarrierRefinement.Construction

noncomputable section

section

/-! A smooth closed carrier becomes integral on an actual ambient open neighborhood of each of its points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_integral_carrier_neighborhood
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (H : X.IdealSheafData) [Smooth (H.subschemeι ≫ f)]
    (x : X) (hx : x ∈ H.support) :
    ∃ U : X.Opens, x ∈ U ∧ IsIntegral (H.comap U.ι).subscheme := by
  have hrange : x ∈ Set.range H.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨y, hy⟩ := hrange
  obtain ⟨C, j, hj, hC, _, z, hz⟩ := Open.ImmersionSmoothImage.Construction.smooth_complex_pointed_integral_chart (H.subschemeι ≫ f) y
  let : IsOpenImmersion j := hj
  let : IsIntegral C := hC
  obtain ⟨O, hO, hpre⟩ := H.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp j.isOpenEmbedding.isOpen_range
  let U : X.Opens := ⟨O, hO⟩
  have hxU : x ∈ U := by
    rw [← hy]
    change y ∈ H.subschemeι ⁻¹' O
    rw [hpre]
    exact ⟨z, hz⟩
  let K := H.comap U.ι
  let m := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H K U.ι rfl
  have hsub : Set.range m ⊆ Set.range j := by
    rintro _ ⟨u, rfl⟩
    rw [← hpre]
    change H.subschemeι (m u) ∈ O
    have he := congrArg (fun a => a u) (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_over H K U.ι rfl)
    change H.subschemeι (m u) = U.ι (K.subschemeι u) at he
    rw [he]
    exact (K.subschemeι u).property
  let l := IsOpenImmersion.lift j m hsub
  have hfac : l ≫ j = m := IsOpenImmersion.lift_fac j m hsub
  let : IsOpenImmersion (l ≫ j) := hfac.symm ▸ inferInstanceAs (IsOpenImmersion m)
  let : IsOpenImmersion l := IsOpenImmersion.of_comp l j
  have hxu : (⟨x, hxU⟩ : U) ∈ Set.range K.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change (⟨x, hxU⟩ : U) ∈ (H.comap U.ι).support
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  obtain ⟨u, _⟩ := hxu
  let : Nonempty K.subscheme := ⟨u⟩
  exact ⟨U, hxU, isIntegral_of_isOpenImmersion l⟩

end

/-! Simultaneously refine a smooth ambient scheme and its smooth closed carrier to integral affine data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_integral_affine_ambient_carrier_refinement
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (H : X.IdealSheafData) [Smooth (H.subschemeι ≫ f)] (x : X) (hx : x ∈ H.support) :
    ∃ (R : CommRingCat) (j : Spec R ⟶ X), IsOpenImmersion j ∧ IsIntegral (Spec R) ∧
      IsIntegral (H.comap j).subscheme ∧ ∃ p : PrimeSpectrum R, j p = x := by
  obtain ⟨U, hxU, hHU⟩ := exists_integral_carrier_neighborhood f H x hx
  let : IsIntegral (H.comap U.ι).subscheme := hHU
  obtain ⟨C, a, ha, hC, _, z, hz⟩ := Open.ImmersionSmoothImage.Construction.smooth_complex_pointed_integral_chart (U.ι ≫ f) (⟨x, hxU⟩ : U)
  let : IsOpenImmersion a := ha
  let : IsIntegral C := hC
  obtain ⟨R, c, hc, p, hp⟩ := Scheme.exists_Spec_apply_eq z
  let : IsOpenImmersion c := hc
  let : Nonempty (Spec R) := ⟨p⟩
  let j0 := c ≫ a
  let j := j0 ≫ U.ι
  have hjpoint : j p = x := by
    change U.ι (a (c p)) = x
    rw [hp, hz]
    rfl
  have hpoint : j0 p ∈ (H.comap U.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change j p ∈ H.support
    rwa [hjpoint]
  have hcarrier : IsIntegral (H.comap j).subscheme := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact IdealSheaf.CarrierBaseChange.Construction.idealSheaf_comap_subscheme_isIntegral (H.comap U.ι) j0 p hpoint
  exact ⟨R, j, inferInstance, isIntegral_of_isOpenImmersion c, hcarrier, p, hjpoint⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.AmbientCarrierRefinement.Construction
