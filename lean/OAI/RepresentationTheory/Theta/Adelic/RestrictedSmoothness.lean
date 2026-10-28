import OAI.RepresentationTheory.Theta.Adelic.LocalGenerators
import OAI.RepresentationTheory.Theta.Adelic.TensorProjective

/-! # Restricted Smoothness -/

namespace OAI.RepresentationTheory.Theta.Adelic.RestrictedSmoothness

noncomputable section

/-! Smoothness of the actual nonarchimedean oscillator action restricted
through a continuous splitting. The proof constructs projective stabilizers
from compact locally constant test functions and Gauss coordinates, then
shrinks to an open subgroup that removes the scalar ambiguity. -/

open OAI.RepresentationTheory.Theta.Adelic.BigCellOne OAI.RepresentationTheory.Theta.Adelic.LocalConstancy
open OAI.RepresentationTheory.Theta.Adelic.LocalKernel OAI.RepresentationTheory.Theta.Adelic.LocalGenerators
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Smoothness Filter
open scoped _root_.Topology

variable {k : Type} [NormedField k] [IsUltrametricDist k] [CharZero k]
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {N : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t : k => ψ t))
    (hu : ∀ t : k, ‖ψ t‖ = 1)

theorem coordinateLift_eigenvector
    (w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (g : BigCellOne.BigCell (k := k) (N := N))
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (hl : Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (BigCellOne.lowerPart g) f.val = f.val)
    (ha : Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator (BigCellOne.linearPart g) f.val = f.val)
    (hr : Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-BigCellOne.upperPart g) (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f).val =
      (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f).val) :
    ∃ z : ℂ, Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (LocalGenerators.coordinateLift ψ hc hu w g) f = z • f := by
  let z : ℂ := (Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k (BigCellOne.linearPart g))))⁻¹
  have hleft : Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ
      (LocalGenerators.quadraticLift ψ hc hu ⟨BigCellOne.lowerPart g, (BigCellOne.parameters_symmetric g).1⟩) f = f :=
    Subtype.ext hl
  have hmiddle : Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (BigCellOne.linearPart g)) f = z • f := by
    apply Subtype.ext
    funext x
    change ((Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (BigCellOne.linearPart g)).val.2 f).val x = z * f.val x
    rw [Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply]
    exact congrArg (z * ·) (congrFun ha x)
  have hquad : Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ
      (LocalGenerators.quadraticLift ψ hc hu ⟨-BigCellOne.upperPart g, (BigCellOne.parameters_symmetric g).2.neg⟩)
      (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f) = Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f := Subtype.ext hr
  have hright : Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ
      (LocalGenerators.upperLift ψ hc hu w ⟨BigCellOne.upperPart g, (BigCellOne.parameters_symmetric g).2⟩) f = f := by
    rw [LocalGenerators.upperLift, map_mul, map_mul, map_inv,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, hquad]
    exact (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w).symm_apply_apply f
  refine ⟨z, ?_⟩
  rw [LocalGenerators.coordinateLift, map_mul, map_mul, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, hright, hmiddle, map_smul, hleft]

theorem coordinateLift_projective_neighborhood
    (w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ∀ᶠ g : BigCellOne.BigCell (k := k) (N := N) in 𝓝 BigCellOne.identity,
      ∃ z : ℂ, Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (LocalGenerators.coordinateLift ψ hc hu w g) f = z • f := by
  have hl := (BigCellOne.lowerPart_continuous.tendsto (BigCellOne.identity (k := k) (N := N))).eventually
    (by simpa only [BigCellOne.lowerPart_identity] using LocalConstancy.quadratic_eventually_fixes ψ hc f)
  have ha := (BigCellOne.linearPart_continuous.tendsto (BigCellOne.identity (k := k) (N := N))).eventually
    (by simpa only [BigCellOne.linearPart_identity] using LocalConstancy.substitution_eventually_fixes f)
  have hr := (BigCellOne.upperPart_continuous.neg.tendsto (BigCellOne.identity (k := k) (N := N))).eventually
    (by simpa only [Pi.neg_apply, BigCellOne.upperPart_identity, neg_zero] using
      LocalConstancy.quadratic_eventually_fixes ψ hc (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f))
  filter_upwards [hl, ha, hr] with g hgl hga hgr
  exact coordinateLift_eigenvector ψ hc hu w g f hgl hga hgr

include hc hu in
theorem local_projective_neighborhood [CompleteSpace k]
    (hk : ¬ DiscreteTopology k) (hn : ∃ t : k, ψ t ≠ 1)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ∀ᶠ a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ in 𝓝 1,
      ∃ z : ℂ, Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f = z • f := by
  obtain ⟨w, hw⟩ := LocalGenerators.exists_weyl_lift ψ hc hu hk hn
  have hbig : ∀ᶠ g : BigCellOne.BigCell (k := k) (N := N) in 𝓝 BigCellOne.identity,
      ∀ a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ, Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a = g.val →
        ∃ z : ℂ, Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f = z • f := by
    filter_upwards [coordinateLift_projective_neighborhood ψ hc hu w f] with g hg
    intro a ha
    obtain ⟨c, hcf⟩ := hg
    obtain ⟨z, hz⟩ := LocalKernel.same_projection_operators hk N ψ hc hu hn a
      (LocalGenerators.coordinateLift ψ hc hu w g)
      (ha.trans (LocalGenerators.coordinateLift_projection ψ hc hu w hw g).symm)
    refine ⟨(z : ℂ) * c, ?_⟩
    rw [hz, hcf, smul_smul]
  have hsymp : ∀ᶠ g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N in 𝓝 1,
      ∀ a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ, Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a = g →
        ∃ z : ℂ, Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f = z • f := by
    have hi := BigCellOne.inclusion_openEmbedding.map_nhds_eq (BigCellOne.identity (k := k) (N := N))
    change Filter.map (Subtype.val : BigCellOne.BigCell (k := k) (N := N) → Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N)
      (𝓝 BigCellOne.identity) = 𝓝 (1 : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) at hi
    rw [← hi]
    exact hbig
  have hp : Tendsto (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ) (𝓝 1) (𝓝 1) := by
    simpa only [map_one] using (Weil.AdelicSplitting.Oscillator.Construction.localProjection_continuous k N ψ).tendsto 1
  filter_upwards [hp.eventually hsymp] with a ha
  exact ha a rfl

include hc hu in
/-- Smoothness is proved after restriction through the supplied continuous
homomorphism. There is no ambient or restricted smoothness premise. -/
theorem restricted_action_smooth [CompleteSpace k]
    (hk : ¬ DiscreteTopology k) (hn : ∃ t : k, ψ t ≠ 1)
    {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    (s : G →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    IsOpen {g : G | Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (s g) f = f} := by
  let S := Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N
  let L := MeasureTheory.Lp ℂ 2 (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
  let : NormedAddCommGroup S :=
    NormedAddCommGroup.induced S L (Weil.UnitarySplitting.Weak.Construction.testToL2 k N) (Weil.UnitarySplitting.Weak.Construction.testToL2_injective k N)
  let : NormedSpace ℂ S := NormedSpace.induced ℂ S L (Weil.UnitarySplitting.Weak.Construction.testToL2 k N)
  let : TopologicalSpace S := (inferInstance : MetricSpace S).toUniformSpace.toTopologicalSpace
  let ρ : G →* (S ≃ₗ[ℂ] S) := (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ).comp s.toMonoidHom
  apply TensorProjective.Smoothness.open_stabilizer_of_projective_neighborhood ρ f
  · have hi : Isometry (Weil.UnitarySplitting.Weak.Construction.testToL2 k N : S → L) :=
      AddMonoidHomClass.isometry_of_norm (Weil.UnitarySplitting.Weak.Construction.testToL2 k N) (fun _ => rfl)
    apply hi.isEmbedding.continuous_iff.mpr
    exact (TensorProjective.Smoothness.local_orbit_L2_continuous k N ψ f).comp s.continuous
  · have hs : Tendsto s (𝓝 (1 : G)) (𝓝 1) := by
      simpa using (show Continuous (fun g : G => s g) from s.continuous).tendsto (1 : G)
    exact hs.eventually (local_projective_neighborhood ψ hc hu hk hn f)

end

end OAI.RepresentationTheory.Theta.Adelic.RestrictedSmoothness
