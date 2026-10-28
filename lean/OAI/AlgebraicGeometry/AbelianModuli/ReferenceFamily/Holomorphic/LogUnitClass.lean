import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogIntegralBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

/-! # Log Unit Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass

noncomputable section

/-! Holomorphic logarithms of genuine transition functions define an
actual degree-one class of the holomorphic unit sheaf. Closure follows
from the integral logarithmic defect and the actual exponential map. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  {I : Type} (U : I → Opens M)
  (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
  (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a))

def holomorphicUnitSection (V : Opens M)
    (s : (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj.obj (.op V)) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := V))ˣ := Additive.toMul s

theorem holomorphicUnit_value_div (V : Opens M)
    (u v : (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := V))ˣ) (x : V) :
    (u / v).val x = u.val x / v.val x := by
  have hi : v.val x * (v⁻¹).val x = 1 :=
    congrArg (fun f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := V) => f x) v.val_inv
  have hv : (v⁻¹).val x = (v.val x)⁻¹ := by
    apply mul_left_cancel₀ (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero v x)
    exact hi.trans (mul_inv_cancel₀ (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero v x)).symm
  change u.val x * (v⁻¹).val x = u.val x / v.val x
  rw [hv, div_eq_mul_inv]

theorem holomorphicUnitSection_value_sub (V : Opens M)
    (s t : (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj.obj (.op V)) (x : V) :
    (holomorphicUnitSection E M V (s - t)).val x =
      (holomorphicUnitSection E M V s).val x / (holomorphicUnitSection E M V t).val x :=
  holomorphicUnit_value_div E M V (holomorphicUnitSection E M V s) (holomorphicUnitSection E M V t) x

def holomorphicLogUnitCech : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicExponentialSheafMap E M).hom 1
    (DivisorClass.Chern.Holomorphic.CechForget.holomorphicCechOfLog E M U l hl)

theorem holomorphicLogUnitCech_closed (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1
      (holomorphicLogUnitCech E M U l hl) = 0 := by
  unfold holomorphicLogUnitCech
  rw [← DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient_delta, DivisorClass.Chern.Holomorphic.LogIntegralBoundary.holomorphicLogCech_integral_boundary E M U l h hl]
  funext a
  change DivisorClass.Chern.Holomorphic.Exponential.holomorphicExpUnit
    (DivisorClass.Chern.Holomorphic.Exponential.holomorphicPeriodFunction (E := E) (DivisorClass.Chern.LogIntegralSheaf.logarithmicIntegerCech (X := TopCat.of M) U l h a)) = 1
  exact DivisorClass.Chern.Holomorphic.Exponential.exp_holomorphicPeriodFunction (DivisorClass.Chern.LogIntegralSheaf.logarithmicIntegerCech (X := TopCat.of M) U l h a)

def holomorphicLogUnitClass (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l)
    (hU : ∀ x, ∃ i, x ∈ U i) : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 (holomorphicLogUnitCech E M U l hl)
      (holomorphicLogUnitCech_closed E M U l hl h)

theorem holomorphicLogUnitCech_apply (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    (holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
      (holomorphicLogUnitCech E M U l hl a)).val x = Complex.exp (l a x) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass
