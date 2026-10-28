import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.BettiSheafCompatibility
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

/-! # Cech Forget -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CechForget

noncomputable section

/-! Forgetting holomorphicity preserves the original literal Cech differential. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicContinuousPresheafMap : (Sheaves.holomorphicFunctionSheaf E M).obj ⟶
    LogCech.RationalCech.continuousComplexPresheaf (TopCat.of M) ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget where
  app U := AddCommGrpCat.ofHom {
    toFun g := ⟨g.val,
      (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ g.val from g.property).continuous⟩
    map_zero' := rfl
    map_add' _ _ := rfl }
  naturality := by
    intro U V i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    rfl

variable {I : Type} (U : I → Opens M)

def holomorphicCechForget (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain (Sheaves.holomorphicFunctionSheaf E M).obj U n) :
    Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf (TopCat.of M)) U n :=
  Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) U (holomorphicContinuousPresheafMap E M) n k

theorem holomorphicCechForget_injective (n : ℕ) :
    Function.Injective (holomorphicCechForget E M U n) := by
  intro k l h
  funext a
  apply ContMDiffMap.ext
  intro x
  exact congrArg (fun c => (c a : C(AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a, ℂ)) x) h

theorem holomorphicCechForget_delta (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain (Sheaves.holomorphicFunctionSheaf E M).obj U n) :
    holomorphicCechForget E M U (n + 1)
        (Abelian.CechCoordinates.abelianCechDelta (Sheaves.holomorphicFunctionSheaf E M).obj U n k) =
      Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf (TopCat.of M)) U n (holomorphicCechForget E M U n k) := by
  unfold holomorphicCechForget
  rw [Abelian.CechClasses.abelianCechCoefficient_delta, Singular.CechSheafification.abelianCechDelta_forget]

def holomorphicCechOfLog (l : LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a)) :
    Abelian.CechCoordinates.AbelianCechCochain (Sheaves.holomorphicFunctionSheaf E M).obj U 1 :=
  fun a => ⟨(l a).toFun, hl a⟩

theorem holomorphicCechOfLog_forget (l : LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a)) :
    holomorphicCechForget E M U 1 (holomorphicCechOfLog E M U l hl) = l := rfl

theorem holomorphicCechForget_period (n : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf (TopCat.of M)) U n) :
    holomorphicCechForget E M U n
      (Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) U (Rational.HolomorphicPeriod.holomorphicRationalPeriodSheafMap E M).hom n k) =
        Rational.Cech.RationalCech.cechCoefficientMap U (LogCech.RationalCech.periodMap (TopCat.of M)) n k := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CechForget
