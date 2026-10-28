import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientCarrierProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SchemeDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierPullbackStep

/-! # Coefficient Program Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

section

/-! The intrinsic coefficient program restricts to the actual pulled-back closed carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.exists_native_coefficient_program_pullback
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H : X.IdealSheafData}
    [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)]
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f J H D P)
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥)
    (hdH : topologicalKrullDim H.subscheme ≤ d)
    {V : Scheme} [IsLocallyNoetherian V] (q : V ⟶ X) [Etale q]
    (H0 : V.IdealSheafData) (hH : H.comap q = H0)
    [IsIntegral H0.subscheme] [CompactSpace H0.subscheme] [Smooth (H0.subschemeι ≫ (q ≫ f))] :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1).factorial H0.subscheme (H0.subschemeι ≫ (q ≫ f))
        (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (q ≫ f) (J.comap q) (n + 1) H0.subschemeι) W k M)
      (r : W ⟶ A.endpoint),
      𝒮.Program schedule (H0.subschemeι ≫ (q ≫ f))
        (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (q ≫ f) (J.comap q) (n + 1) H0.subschemeι)
        (fun l => ((D l).comap q).comap H0.subschemeι) Q ∧
      A.coefficientPrefix.EtaleComparison Q (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H H0 q hH) r := by
  let p := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H H0 q hH
  let C0 := GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (q ≫ f) (J.comap q) (n + 1) H0.subschemeι
  let : IsLocallyNoetherian H0.subscheme := LocallyOfFiniteType.isLocallyNoetherian H0.subschemeι
  have he : (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι).comap p = C0 :=
    Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothCoefficientIdealSheaf_comap_etale_square f J (n + 1) H.subschemeι H0.subschemeι q p
      (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_over H H0 q hH)
  have hC0 : C0 ≠ ⊥ := he ▸ Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_nonempty_etale_ne_bot p _ hC
  have hg : p ≫ (H.subschemeι ≫ f) = H0.subschemeι ≫ (q ≫ f) := by
    rw [← Category.assoc, IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_over, Category.assoc]
  have hD : ∀ l, ((D l).comap H.subschemeι).comap p = ((D l).comap q).comap H0.subschemeι := by
    intro l
    rw [← Scheme.IdealSheafData.comap_comp, IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_over, Scheme.IdealSheafData.comap_comp]
  exact 𝒮.pullback (Nat.factorial_pos _) A.program H0.subscheme
    (Blowups.Etale.SchemeDimension.Construction.scheme_dimension_le_of_etale p d hdH) (H0.subschemeι ≫ (q ≫ f)) C0 hC0
    (fun l => ((D l).comap q).comap H0.subschemeι) p hg he hD

end

section

/-! Every actual ambient restriction retains its intrinsic coefficient-program certificate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.exists_on_etale_comparison
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H : X.IdealSheafData}
    [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)]
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f J H D P)
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥)
    (hdH : topologicalKrullDim H.subscheme ≤ d)
    {V W : Scheme} [IsLocallyNoetherian V] (q : V ⟶ X) [Etale q]
    (H0 : V.IdealSheafData) (hH : H.comap q = H0)
    [IsIntegral H0.subscheme] [CompactSpace H0.subscheme] [Smooth (H0.subschemeι ≫ (q ≫ f))]
    {h : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : W.IdealSheafData}
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V (q ≫ f) (J.comap q) W h L)
    (r : W ⟶ Y) (hc : P.EtaleComparison Q q r) :
    Nonempty (CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule (q ≫ f) (J.comap q) H0
      (fun l => (D l).comap q) Q) := by
  obtain ⟨Z, k, M, R, s, hR, hs⟩ := A.exists_native_coefficient_program_pullback hC hdH q H0 hH
  obtain ⟨t, ht, _⟩ := P.carrierPullback A.coefficientPrefix H.subschemeι A.carrierMap A.comparison
    Q R H0.subschemeι (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H H0 q hH) s q r hc hs
    (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_isPullback H H0 q hH)
  exact ⟨{ endpoint := Z
           structureMap := k
           ideal := M
           coefficientPrefix := R
           program := hR
           carrierMap := t
           comparison := ht }⟩

end

/-! Carrier-program restriction with the source structure map and marked ideal named independently. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.exists_on_etale_comparison_to
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H : X.IdealSheafData}
    [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)]
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f J H D P)
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥)
    (hdH : topologicalKrullDim H.subscheme ≤ d)
    {V W : Scheme} [IsLocallyNoetherian V] (q : V ⟶ X) [Etale q]
    (f0 : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f0] (J0 H0 : V.IdealSheafData)
    (hf : q ≫ f = f0) (hJ : J.comap q = J0) (hH : H.comap q = H0)
    [IsIntegral H0.subscheme] [CompactSpace H0.subscheme] [Smooth (H0.subschemeι ≫ f0)]
    {h : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : W.IdealSheafData}
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V f0 J0 W h L)
    (r : W ⟶ Y) (hc : P.EtaleComparison Q q r) :
    Nonempty (CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f0 J0 H0 (fun l => (D l).comap q) Q) := by
  subst f0
  subst J0
  exact A.exists_on_etale_comparison hC hdH q H0 hH Q r hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
