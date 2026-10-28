import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientCarrierProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientPrefixLift
import OAI.AlgebraicGeometry.Resolution.Blowups.InitialRetractedCoefficientCover
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierDimensionClearance

/-! # Uniform Coefficient Carrier Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.UniformCoefficientCarrierPrograms.Construction

noncomputable section

/-! An established uniform control system in dimension d constructs common intrinsic carrier programs in dimension d+1. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_uniform_coefficient_carrier_programs
    {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (n : ℕ)
    {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J H : ∀ i, (X i).IdealSheafData)
    [∀ i, IsIntegral (H i).subscheme] [∀ i, Smooth ((H i).subschemeι ≫ f i)]
    (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ)) (D : ∀ i, β → (X i).IdealSheafData)
    (A : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i)
      (fun j : Option β => match j with | none => H i | some l => D i l) [Finset.univ])
    (htangent : ∀ i, H i ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) n)
    (hC : ∀ i, GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (f i) (J i) (n + 1) (H i).subschemeι ≠ ⊥) :
    ∃ s : 𝒮.Schedule (n + 1).factorial β, ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
        Nonempty (Uniform.CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 s (f i) (J i) (H i) (D i) P) ∧
        P.HasIncidenceTrace β (D i) (𝒮.incidenceTrace s) ∧
        (letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤) := by
  let : ∀ i, IsLocallyNoetherian (H i).subscheme := fun i => LocallyOfFiniteType.isLocallyNoetherian (H i).subschemeι
  let : ∀ i, CompactSpace (H i).subscheme := fun i => QuasiCompact.compactSpace_of_compactSpace (H i).subschemeι
  let C (i : ι) := GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (f i) (J i) (n + 1) (H i).subschemeι
  have hdH (i : ι) : topologicalKrullDim (H i).subscheme ≤ d :=
    Global.CartierDimension.Construction.locallyPrincipal_subscheme_dimension_le (H i) ((A i).component_ne_bot none)
      ((A i).component_locallyPrincipal none) d (hd i)
  obtain ⟨s, hprograms⟩ := 𝒮.finitePrograms (n + 1).factorial (Nat.factorial_pos _)
    (fun i => (H i).subscheme) (fun i => (H i).subschemeι ≫ f i) C hC hdH
    (fun i l => (D i l).comap (H i).subschemeι) (fun i => (A i).componentCarrier)
  refine ⟨s, ?_⟩
  intro i
  obtain ⟨V, h, L, Q, hQ⟩ := hprograms i
  obtain ⟨Y, g, K, P, r, hr, htrace, _, ht⟩ := Uniform.CoefficientPrefixLift.Construction.exists_uniform_carrier_lift_of_bounded_coefficient_prefix
    n Q.stepCount (X i) (f i) (J i) (H i) ((A i).component_ne_bot none)
    ((A i).component_locallyPrincipal none) (htangent i) (C i) (hC i) le_rfl
    (InitialRetractedCoefficientCover.Construction.exists_initial_retracted_global_coefficient_cover (f i) (J i) (H i)
      ((A i).component_ne_bot none) ((A i).component_locallyPrincipal none) (n + 1))
    Q le_rfl β (D i) (A i) (𝒮.incidenceTrace s) (𝒮.hasTrace hQ) (𝒮.terminal (Nat.factorial_pos _) hQ)
  exact ⟨Y, g, K, P, ⟨{
    endpoint := V
    structureMap := h
    ideal := L
    coefficientPrefix := Q
    program := hQ
    carrierMap := r
    comparison := hr }⟩, htrace, ht⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.UniformCoefficientCarrierPrograms.Construction
