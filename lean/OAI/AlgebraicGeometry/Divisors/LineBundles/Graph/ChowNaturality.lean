import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentPullbackPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentCycles
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowFamilyClass

/-! # Chow Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowNaturality.BundleCycles

noncomputable section

/-! The independently constructed geometric cycle class commutes with the actual graph Chow pullback for every morphism of smooth projective presentations, including disconnected and empty schemes and components of different dimensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

theorem graphChowPullback_cycleClass (α : Chow.BundleCycles.ChowQ Y p) :
    Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p (ChowPullback.BundleCycles.graphChowPullback f p α) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p α) := by
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective Y p α
  apply X.componentBetti_ext (ModuleCat.of ℚ ℚ) (p + p)
  intro C
  let D := Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C
  let g := Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C
  let a := X.componentInclusionOver C
  let b := Y.componentInclusionOver D
  let β := Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z))
  let w := GraphNormal.InverseChow.BundleCycles.graphNormalPointPreimage f β
  have hw : ChowPullback.BundleCycles.graphChowPullback f p (Chow.BundleCycles.cycleToChowQ Y p z) = Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p w :=
    ChowPullback.BundleCycles.graphChowPullback_cycle f p z
  have hx := PresentationComponentCycles.Bundle.geometricCycleClassQ_component_pointClass X C p w
  have hp := ComponentPullbackPreimage.BundleCycles.graphComponentPullback_preimage f C p z
  have hi := ChowFamilyClass.BundleCycles.graphChowPullback_cycleClass_integral g p
    (Chow.BundleCycles.cycleToChowQ (Y.componentVariety D).presentation p (PresentationComponentCycles.Bundle.presentationComponentCycle Y D p z))
  have hy := PresentationComponentCycles.Bundle.presentationComponentCycle_class Y D p z
  have hm := (Conormal.BundleCycles.bettiMap_comp (ModuleCat.of ℚ ℚ) (p + p) a f).symm.trans
    ((congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p)) (ComponentAmbient.BundleCycles.projectiveMorphismOnComponentOver_square f C)).trans
      (Conormal.BundleCycles.bettiMap_comp (ModuleCat.of ℚ ℚ) (p + p) g b))
  have hc := ConcreteCategory.congr_hom hm (Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p (Chow.BundleCycles.cycleToChowQ Y p z))
  exact (congrArg (fun q => Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) a (Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p q)) hw).trans
    (hx.trans
      ((congrArg (Geometric.CycleClass.BundleCycles.geometricCycleClassQ (X.componentVariety C).presentation p) hp.symm).trans
        (hi.trans
          (hc.trans (congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) g) hy)).symm)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowNaturality.BundleCycles
