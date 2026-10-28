import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality

/-! # Presentation Pullback Purity -/

namespace OAI.AlgebraicTopology.Kunneth.PresentationPullbackPurity

noncomputable section

/-! Algebraic pullback preserves the actual componentwise pure subspaces on all presentations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

namespace Constructions

theorem integralMorphism_factors_component (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : V.toOver ⟶ P.toOver) :
    ∃ C : irreducibleComponents P.carrier,
      ∃ g : V.toOver ⟶ (P.componentVariety C).toOver, g ≫ P.componentInclusionOver C = f := by
  have hr : IsIrreducible (Set.range f.left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ V.carrier).image f.left
        f.left.continuous.continuousOn
  obtain ⟨C, hC, hf⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hr
  let c : irreducibleComponents P.carrier := ⟨C, hC⟩
  have hrange : Set.range f.left ⊆ Set.range (P.componentInclusion c) := by
    rw [P.componentInclusion_range]
    exact hf
  let g := IsOpenImmersion.lift (P.componentInclusion c) f.left hrange
  have hfac : g ≫ P.componentInclusion c = f.left := IsOpenImmersion.lift_fac _ _ hrange
  have hover : g ≫ (P.componentVariety c).structureMap = V.structureMap := by
    rw [← P.componentInclusion_over c, ← Category.assoc, hfac]
    exact f.w
  refine ⟨c, Over.homMk g hover, ?_⟩
  apply Over.OverMorphism.ext
  exact hfac

theorem schemeBettiMap_comp_apply {R : Type} [Ring R] (N : ModuleCat R) (n : ℕ)
    {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z) (a : AlgebraicGeometry.Betti.Scheme.schemeBetti N Z n) :
    AlgebraicGeometry.Betti.Scheme.schemeBettiMap N n (f ≫ g) a = AlgebraicGeometry.Betti.Scheme.schemeBettiMap N n f (AlgebraicGeometry.Betti.Scheme.schemeBettiMap N n g a) := by
  exact ConcreteCategory.congr_hom ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor N n).map_comp g.op f.op) a

theorem integralPullback_mem_presentationPure (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : V.toOver ⟶ P.toOver) (p q : ℕ)
    (a : P.complexCohomology (p + q)) (ha : a ∈ P.pureBettiSubspace p q) :
    AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + q) f a ∈ V.pureBettiSubspace p q := by
  obtain ⟨C, g, hfac⟩ := integralMorphism_factors_component V P f
  have hc := (P.mem_pureBettiSubspace_iff p q a).mp ha C
  rw [P.componentBettiEquiv_apply] at hc
  have h := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace g p q hc
  rw [← hfac, schemeBettiMap_comp_apply]
  exact h

theorem presentationPullback_mem_pure (P Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : P.toOver ⟶ Q.toOver) (p q : ℕ) (a : Q.complexCohomology (p + q))
    (ha : a ∈ Q.pureBettiSubspace p q) :
    AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + q) f a ∈ P.pureBettiSubspace p q := by
  apply (P.mem_pureBettiSubspace_iff p q _).mpr
  intro C
  rw [P.componentBettiEquiv_apply, ← schemeBettiMap_comp_apply]
  exact integralPullback_mem_presentationPure (P.componentVariety C) Q
    (P.componentInclusionOver C ≫ f) p q a ha

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.PresentationPullbackPurity
