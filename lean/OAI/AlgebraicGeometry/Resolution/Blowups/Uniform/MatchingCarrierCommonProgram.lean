import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CarrierCommonAmbientProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CommonCarrierPullbackData

/-! # Matching Carrier Common Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Matching smooth carriers and ambient ideals construct an actual common ambient program. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ControlProgramSystem.Construction.UniformControlProgramSystem.exists_common_ambient_program_on_matching_carriers {d : ℕ} (𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d)
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
    (S : Scheme) [IsIntegral S] [IsLocallyNoetherian S]
    (a b : S ⟶ X) [Etale a] [Etale b]
    (hf : a ≫ f = b ≫ f) (hJ : J.comap a = J.comap b) (hH : H.comap a = H'.comap b)
    (hD : ∀ l, (D l).comap a = (D l).comap b)
    [IsIntegral (H.comap a).subscheme] [CompactSpace (H.comap a).subscheme]
    (hdH : topologicalKrullDim H.subscheme ≤ d) :
    ∃ (S' : Scheme) (s : S' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (B : S'.IdealSheafData)
      (P0 : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) S (a ≫ f) (J.comap a) S' s B)
      (u : S' ⟶ Y) (u' : S' ⟶ Y'), P.EtaleComparison P0 a u ∧ P'.EtaleComparison P0 b u' := by
  obtain ⟨A⟩ := Dimension.CommonCarrierPullbackData.Construction.exists_dimension_common_carrier_pullback_data d f J H H' C C' (n + 1) hC hCdef hC'def D a b
    hf hJ hH hD hdH
  let : Smooth A.structureMap := A.left_structure ▸ inferInstanceAs (Smooth (A.left ≫ (H.subschemeι ≫ f)))
  exact 𝒮.exists_common_ambient_program (Nat.factorial_pos _) P Q P' Q' T T' H.subschemeι r H'.subschemeι r' hc hc'
    S A.carrier A.dimension (a ≫ f) A.structureMap (J.comap a) A.ideal A.ideal_ne_bot A.boundary A.carrierMap
    a b A.left A.right rfl hf.symm A.left_structure A.right_structure rfl hJ.symm
    A.left_ideal A.right_ideal A.left_boundary A.right_boundary A.left_pullback A.right_pullback

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
