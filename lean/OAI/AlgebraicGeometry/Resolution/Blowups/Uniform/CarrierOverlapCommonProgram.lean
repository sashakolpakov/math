import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientProgramPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicCarrierRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CarrierTangentDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.EtalePullbackExistence

/-! # Carrier Overlap Common Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Initial tangent comparisons on an overlap construct a common actual program for two carrier choices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.exists_common_program_on_tangent_overlap
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X X' Y Y' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f']
    {J H : X.IdealSheafData} {J' H' : X'.IdealSheafData}
    [IsIntegral H.subscheme] [IsIntegral H'.subscheme]
    [Smooth (H.subschemeι ≫ f)] [Smooth (H'.subschemeι ≫ f')]
    {D : β → X.IdealSheafData} {D' : β → X'.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K} {P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X' f' J' Y' g' K'}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f J H D P)
    (A' : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f' J' H' D' P')
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥)
    (hC' : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f' J' (n + 1) H'.subschemeι ≠ ⊥)
    (hdH : topologicalKrullDim H.subscheme ≤ d) (hdH' : topologicalKrullDim H'.subscheme ≤ d)
    (hmax : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    {S : Scheme} [IsIntegral S] [IsLocallyNoetherian S]
    (v : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth v] (L H0 H1 : S.IdealSheafData) (E : β → S.IdealSheafData)
    [IsIntegral H0.subscheme] [IsIntegral H1.subscheme]
    [CompactSpace H0.subscheme] [CompactSpace H1.subscheme]
    (a : S ⟶ X) (b : S ⟶ X') [Etale a] [Etale b]
    (haf : a ≫ f = v) (hbf : b ≫ f' = v)
    (haJ : J.comap a = L) (hbJ : J'.comap b = L)
    (haH : H.comap a = H0) (hbH : H'.comap b = H1)
    (haD : ∀ l, (D l).comap a = E l) (hbD : ∀ l, (D' l).comap b = E l)
    (hcompare : ∀ x : S, x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf v L n).support →
      Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt v L H0 H1 E n x)) :
    ∃ (W : Scheme) (w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) S v L W w M) (r : W ⟶ Y) (s : W ⟶ Y'),
      P.EtaleComparison R a r ∧ P'.EtaleComparison R b s := by
  obtain ⟨Z, z, B, R, r, hr⟩ := P.exists_etale_pullback S v L a haf haJ
  obtain ⟨Z', z', B', R', r', hr'⟩ := P'.exists_etale_pullback S v L b hbf hbJ
  let : Smooth (H0.subschemeι ≫ v) := IntrinsicCarrierRestriction.Construction.native_carrier_restriction_smooth f H a v H0 haf haH
  let : Smooth (H1.subschemeι ≫ v) := IntrinsicCarrierRestriction.Construction.native_carrier_restriction_smooth f' H' b v H1 hbf hbH
  have hA0 := A.exists_on_etale_comparison_to hC hdH a v L H0 haf haJ haH R r hr
  have hA1 := A'.exists_on_etale_comparison_to hC' hdH' b v L H1 hbf hbJ hbH R' r' hr'
  rw [funext haD] at hA0
  rw [funext hbD] at hA1
  obtain ⟨A0⟩ := hA0
  obtain ⟨A1⟩ := hA1
  have hC0 := IntrinsicCarrierRestriction.Construction.native_carrier_restriction_coefficient_ne_bot f J H (n + 1) hC a v L H0 haf haJ haH
  have hmax0 := IntrinsicCarrierRestriction.Construction.native_carrier_restriction_tangent f J H n hmax a v L H0 haf haJ haH
  have hdH0 := Blowups.Etale.SchemeDimension.Construction.scheme_dimension_le_of_etale (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H H0 a haH) d hdH
  obtain ⟨e, he, _⟩ := A0.exists_endpointIso_of_tangent_comparisons A1 hC0 hmax0 hdH0 hcompare
  have hcomp := hr.comp P R a r R' (𝟙 S) e.hom he
  rw [Category.id_comp] at hcomp
  exact ⟨Z', z', B', R', e.hom ≫ r, r', hcomp, hr'⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
