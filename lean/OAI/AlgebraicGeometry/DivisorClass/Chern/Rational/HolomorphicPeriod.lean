import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! # Holomorphic Period -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod

noncomputable section

/-! Rationalization of the actual integral period map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def rationalConstantAbelianSheaf (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat)).obj
    (ConstantSheaf.RationalCech.locallyConstantRationalSheaf X)

def integralToRationalConstantSheaf (X : TopCat.{0}) :
    IntegralConstantSheaf.integralConstantSheaf X ⟶ rationalConstantAbelianSheaf X :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom {
      toFun n := ⟨fun x => (n x : ℚ), n.isLocallyConstant.comp (fun z : ℤ => (z : ℚ))⟩
      map_zero' := by apply LocallyConstant.ext; intro x; simp
      map_add' := by
        intro n m
        apply LocallyConstant.ext
        intro x
        change ((n x + m x : ℤ) : ℚ) = (n x : ℚ) + (m x : ℚ)
        exact Int.cast_add _ _ }
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro n
      apply LocallyConstant.ext
      intro x
      rfl }

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicRationalPeriodFunction (q : LocallyConstant M ℚ) :
    Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M) :=
  ⟨fun x => (q x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I), by
    intro x
    apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [q.isLocallyConstant.eventually_eq x] with y hy
    change q y = q x at hy
    rw [hy]⟩

def holomorphicRationalPeriod : LocallyConstant M ℚ →+ Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M) where
  toFun := holomorphicRationalPeriodFunction
  map_zero' := by
    apply ContMDiffMap.ext
    intro x
    simp [holomorphicRationalPeriodFunction]
  map_add' q r := by
    apply ContMDiffMap.ext
    intro x
    change ((q x + r x : ℚ) : ℂ) * _ = _
    rw [Rat.cast_add, add_mul]
    rfl

variable (E M)

def holomorphicRationalPeriodSheafMap :
    rationalConstantAbelianSheaf (TopCat.of M) ⟶ Holomorphic.Sheaves.holomorphicFunctionSheaf E M :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (holomorphicRationalPeriod (E := E) (M := U.unop))
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro q
      apply ContMDiffMap.ext
      intro x
      rfl }

theorem integralToRationalConstantSheaf_period :
    integralToRationalConstantSheaf (TopCat.of M) ≫ holomorphicRationalPeriodSheafMap E M =
      Holomorphic.PeriodSequence.holomorphicPeriodSheafMap E M := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  change LocallyConstant U.unop ℤ at n
  apply ContMDiffMap.ext
  intro x
  change (((n x : ℤ) : ℚ) : ℂ) * _ = (n x : ℂ) * _
  rw [Rat.cast_intCast]

abbrev rationalSheafCohomologyTwo := CategoryTheory.Sheaf.H (rationalConstantAbelianSheaf (TopCat.of M)) 2

def integralToRationalSheafCohomology : Holomorphic.Connecting.integralSheafCohomologyTwo M →+ rationalSheafCohomologyTwo M :=
  CategoryTheory.Sheaf.H.map (integralToRationalConstantSheaf (TopCat.of M)) 2

def rationalHolomorphicObstruction : rationalSheafCohomologyTwo M →+
    CategoryTheory.Sheaf.H (Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 2 :=
  CategoryTheory.Sheaf.H.map (holomorphicRationalPeriodSheafMap E M) 2

theorem holomorphicPeriodCohomologyMap_factor (a : Holomorphic.Connecting.integralSheafCohomologyTwo M) :
    Holomorphic.Connecting.holomorphicPeriodCohomologyMap E M a =
      rationalHolomorphicObstruction E M (integralToRationalSheafCohomology M a) := by
  change CategoryTheory.Sheaf.H.map (Holomorphic.PeriodSequence.holomorphicPeriodSheafMap E M) 2 a = _
  rw [← integralToRationalConstantSheaf_period, CategoryTheory.Sheaf.H.map_comp_apply]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod
