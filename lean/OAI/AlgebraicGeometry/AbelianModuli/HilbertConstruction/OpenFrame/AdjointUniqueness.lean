import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointRecovery

/-! # Adjoint Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointUniqueness

noncomputable section

/-! The explicit pulled-back frame sheaf has the uniqueness part of the pullback universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)

theorem openFramePullbackAdjoint_generator_one (W : Y.Opens) (i : ι) (hi : W ≤ U i) :
    (PullbackSheafMap.openFramePullbackAdjoint D f).app W (SectionGenerators.openFrameGenerator D W i hi 1) =
      SectionGenerators.openFrameGenerator (D.pullback f) (f ⁻¹ᵁ W) i ((TopologicalSpace.Opens.map f.base).monotone hi) 1 :=
  (PullbackGenerators.openFrameSectionPullback_generator D f W i hi 1).trans
    (congrArg (SectionGenerators.openFrameGenerator (D.pullback f) (f ⁻¹ᵁ W) i ((TopologicalSpace.Opens.map f.base).monotone hi))
      ((f.app W).hom.map_one))

theorem openFrameAdjointLift_unique (hU : ∀ y : Y, ∃ i, y ∈ U i)
    {N : X.Modules} (β : ModuleSheaf.openFrameModuleSheaf D ⟶ (Scheme.Modules.pushforward f).obj N)
    (φ : ModuleSheaf.openFrameModuleSheaf (D.pullback f) ⟶ N)
    (hφ : PullbackSheafMap.openFramePullbackAdjoint D f ≫ (Scheme.Modules.pushforward f).map φ = β) :
    φ = AdjointLift.openFrameAdjointLift D f hU β := by
  apply (AdjointFrameCompatibility.adjointCompatibleFrameImages D f β).glue_unique (ConstructedCompatibleFrames.openFrameSheafFrames (D.pullback f))
    (PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover f hU)
  intro V i hi r
  have he := congrArg (fun g : ModuleSheaf.openFrameModuleSheaf D ⟶ (Scheme.Modules.pushforward f).obj N =>
    g.app (U i) (SectionGenerators.openFrameGenerator D (U i) i le_rfl 1)) hφ
  have hf := (congrArg (φ.app (f ⁻¹ᵁ U i)) (openFramePullbackAdjoint_generator_one D f (U i) i le_rfl)).symm.trans he
  have hn := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hi).op)
    (SectionGenerators.openFrameGenerator (D.pullback f) (f ⁻¹ᵁ U i) i le_rfl 1)
  have hg : (ModuleSheaf.openFrameModuleSheaf (D.pullback f)).presheaf.map (homOfLE hi).op
      (SectionGenerators.openFrameGenerator (D.pullback f) (f ⁻¹ᵁ U i) i le_rfl 1) =
      SectionGenerators.openFrameGenerator (D.pullback f) V i hi 1 :=
    (GeneratorNaturality.openFrameGenerator_restriction (D.pullback f) hi i le_rfl 1).trans
      (congrArg (SectionGenerators.openFrameGenerator (D.pullback f) V i hi) ((X.presheaf.map (homOfLE hi).op).hom.map_one))
  have hp : φ.app V (SectionGenerators.openFrameGenerator (D.pullback f) V i hi 1) = AdjointFrameImages.adjointFrameImage D f β V i hi :=
    (congrArg (φ.app V) hg).symm.trans (hn.trans (congrArg (N.presheaf.map (homOfLE hi).op) hf))
  exact (congrArg (φ.app V) (GeneratorNaturality.openFrameGenerator_smul_one (D.pullback f) V i hi r).symm).trans
    ((φ.app_smul r (SectionGenerators.openFrameGenerator (D.pullback f) V i hi 1)).trans
      (congrArg (fun a : Γ(N, V) => r • a) hp))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointUniqueness
