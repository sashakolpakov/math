import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformAtlasPointedPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformAtlasFiniteRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonOpen

/-! # Uniform Atlas Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled

noncomputable section

/-! A nonterminal étale restriction retains a finite modeled normal atlas with the same intrinsic coefficient schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram.exists_on_etale_comparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y V W : Scheme} [CompactSpace V] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : Y.IdealSheafData} {M : W.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y g K}
    (A : UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram 𝒮 schedule f J D P) (q : V ⟶ X) [Etale q]
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V (q ≫ f) (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n) W k M)
    (r : W ⟶ Y) (hc : P.EtaleComparison Q q r)
    (hne : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) n ≠ ⊤) :
    Nonempty (UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram 𝒮 schedule (q ≫ f) (J.comap q)
      (fun l => (D l).comap q) Q) := by
  apply UniformAtlasFiniteRefinement.Construction.exists_modeled_uniform_atlas_of_pointed_programs
    (hc.hasIncidenceTrace P Q q r β D (𝒮.incidenceTrace schedule) A.trace)
    (hc.endpoint_order_bound P Q q r n A.terminal) hne
  exact A.exists_chart_on_etale_comparison q Q r hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled
