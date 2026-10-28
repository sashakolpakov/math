import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.MatchingCarrierCommonProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.AmbientCarrierRefinement

/-! # Pointed Carrier Common Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Refine any pointed matching carrier comparison to an actual common complete ambient program. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ControlProgramSystem.Construction.UniformControlProgramSystem.exists_pointed_common_ambient_program {d : ℕ} (𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y Y' W W' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k' : W' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J H H' : X.IdealSheafData} [IsIntegral H.subscheme]
    [Smooth (H.subschemeι ≫ f)] [Smooth (H'.subschemeι ≫ f)]
    {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    (C : H.subscheme.IdealSheafData) (C' : H'.subscheme.IdealSheafData)
    (hC : C ≠ ⊥) (hCdef : C = GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι)
    (hC'def : C' = GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H'.subschemeι)
    {M : W.IdealSheafData} {M' : W'.IdealSheafData} (D : β → X.IdealSheafData)
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) (P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y' g' K')
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1).factorial H.subscheme (H.subschemeι ≫ f) C W k M)
    (Q' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1).factorial H'.subscheme (H'.subschemeι ≫ f) C' W' k' M')
    (T : 𝒮.Program schedule (H.subschemeι ≫ f) C (fun l => (D l).comap H.subschemeι) Q)
    (T' : 𝒮.Program schedule (H'.subschemeι ≫ f) C' (fun l => (D l).comap H'.subschemeι) Q')
    (r : W ⟶ Y) (r' : W' ⟶ Y') (hc : P.CarrierComparison Q H.subschemeι r)
    (hc' : P'.CarrierComparison Q' H'.subschemeι r')
    (S : Scheme) (a b : S ⟶ X) [Etale a] [Etale b]
    (hf : a ≫ f = b ≫ f) (hJ : J.comap a = J.comap b) (hH : H.comap a = H'.comap b)
    (hD : ∀ l, (D l).comap a = (D l).comap b)
    (hdH : topologicalKrullDim H.subscheme ≤ d) (x : S) (hx : a x ∈ H.support) :
    ∃ (R : CommRingCat) (j : Spec R ⟶ S), IsOpenImmersion j ∧
      ∃ p : PrimeSpectrum R, j p = x ∧
        ∃ (S' : Scheme) (s : S' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (B : S'.IdealSheafData)
          (P0 : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec R) ((j ≫ a) ≫ f) (J.comap (j ≫ a)) S' s B)
          (u : S' ⟶ Y) (u' : S' ⟶ Y'),
          P.EtaleComparison P0 (j ≫ a) u ∧ P'.EtaleComparison P0 (j ≫ b) u' := by
  let H0 := H.comap a
  let : Smooth (H0.subschemeι ≫ (a ≫ f)) := Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_etale_smooth_center f a H
  have hx0 : x ∈ H0.support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  obtain ⟨R, j, hj, hR, hHR, p, hp⟩ := Integral.AmbientCarrierRefinement.Construction.exists_integral_affine_ambient_carrier_refinement (a ≫ f) H0 x hx0
  let : IsOpenImmersion j := hj
  let : IsIntegral (Spec R) := hR
  let : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian ((j ≫ a) ≫ f)
  let : IsIntegral (H.comap (j ≫ a)).subscheme := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact hHR
  let : CompactSpace (H.comap (j ≫ a)).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (H.comap (j ≫ a)).subschemeι
  have hf0 : (j ≫ a) ≫ f = (j ≫ b) ≫ f := by rw [Category.assoc, Category.assoc, hf]
  have hJ0 : J.comap (j ≫ a) = J.comap (j ≫ b) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hJ]
  have hH0 : H.comap (j ≫ a) = H'.comap (j ≫ b) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hH]
  have hD0 (l : β) : (D l).comap (j ≫ a) = (D l).comap (j ≫ b) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hD l]
  obtain ⟨S', s, B, P0, u, u', haP, hbP⟩ :=
    𝒮.exists_common_ambient_program_on_matching_carriers C C' hC hCdef hC'def D P P' Q Q' T T' r r' hc hc'
      (Spec R) (j ≫ a) (j ≫ b) hf0 hJ0 hH0 hD0 hdH
  exact ⟨R, j, hj, p, hp, S', s, B, P0, u, u', haP, hbP⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
