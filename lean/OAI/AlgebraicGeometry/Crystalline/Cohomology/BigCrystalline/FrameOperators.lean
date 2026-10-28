import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Constants

/-! # Frame Operators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators.BigCrystallineFrameOperators

noncomputable section

/-! # Coordinate operators on original big crystalline frame functions -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps.BigCrystallineFrameMaps OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor.BigCrystallineFrameFunctor

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)} (a : σ → A)

def derivative (i : σ) : FrameFunctor.BigCrystallineFrameFunctor.functions (p := p) (J := J) (δ := δ) (base := base) a ⟶
    FrameFunctor.BigCrystallineFrameFunctor.functions (p := p) (J := J) (δ := δ) (base := base) a where
  app Q := ModuleCat.ofHom ((FreeDivided.Derivation.FreeDividedDerivation.derivation Q.unop.ring σ i).toLinearMap.restrictScalars W)
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    let : Algebra Q.unop.ring P.unop.ring := f.unop.ringMap.toRingHom.toAlgebra
    exact Divided.AffineMaps.DividedAffineMaps.derivation_naturality Q.unop.ring P.unop.ring σ
      P.unop.ideal P.unop.dividedPowers (FrameLifts.BigCrystallineFrameLifts.translation a f.unop) (FrameLifts.BigCrystallineFrameLifts.translation_mem a f.unop) i t

def primitive (Q : (FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base)ᵒᵖ) (i : σ) : Module.End W ((FrameFunctor.BigCrystallineFrameFunctor.functions a).obj Q) :=
  (FreeDivided.Primitive.FreeDividedPrimitive.primitive Q.unop.ring σ i).restrictScalars W

def retraction (Q : (FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base)ᵒᵖ) : (FrameFunctor.BigCrystallineFrameFunctor.functions a).obj Q →ₗ[W]
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
      (p := p) (J := J) (δ := δ) base).obj Q :=
  (FreeDivided.Constants.FreeDividedConstants.constantCoefficient Q.unop.ring σ).restrictScalars W

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators.BigCrystallineFrameOperators
