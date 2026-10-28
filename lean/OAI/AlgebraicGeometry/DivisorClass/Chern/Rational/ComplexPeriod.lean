import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultComparison

/-! # Complex Period -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexPeriod

noncomputable section

/-! The original rational period obstruction factors through actual complex locally constant coefficients. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def rationalConstantComplexSheafMap (X : TopCat.{0}) :
    HolomorphicPeriod.rationalConstantAbelianSheaf X ⟶ Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf X :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom {
      toFun (f : LocallyConstant U.unop ℚ) :=
        ⟨fun x => (f x : ℂ), f.isLocallyConstant.comp (fun q : ℚ => (q : ℂ))⟩
      map_zero' := by apply LocallyConstant.ext; intro x; exact Rat.cast_zero
      map_add' := by
        intro f g
        change LocallyConstant U.unop ℚ at f g
        apply LocallyConstant.ext
        intro x
        exact Rat.cast_add (f x) (g x) }
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      apply LocallyConstant.ext
      intro x
      rfl }

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicScalarSheafMap (z : ℂ) : Holomorphic.Sheaves.holomorphicFunctionSheaf E M ⟶ Holomorphic.Sheaves.holomorphicFunctionSheaf E M :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom {
      toFun (f : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop)) := z • f
      map_zero' := by
        apply ContMDiffMap.ext
        intro x
        exact mul_zero z
      map_add' := by
        intro f g
        apply ContMDiffMap.ext
        intro x
        change z * (f x + g x) = z * f x + z * g x
        exact mul_add z (f x) (g x) }
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      apply ContMDiffMap.ext
      intro x
      rfl }

theorem holomorphicRationalPeriodSheafMap_factor_complex :
    HolomorphicPeriod.holomorphicRationalPeriodSheafMap E M =
      rationalConstantComplexSheafMap (TopCat.of M) ≫
        Manifold.DolbeaultComparison.locallyConstantComplexHolomorphicSheafMap (E := E) (M := M) ≫
          holomorphicScalarSheafMap (E := E) (M := M) (2 * (Real.pi : ℂ) * Complex.I) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  change LocallyConstant U.unop ℚ at f
  apply ContMDiffMap.ext
  intro x
  change (f x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
    (2 * (Real.pi : ℂ) * Complex.I) * (f x : ℂ)
  exact mul_comm _ _

theorem rationalHolomorphicObstruction_zero_of_complex
    (a : HolomorphicPeriod.rationalSheafCohomologyTwo M)
    (ha : CategoryTheory.Sheaf.H.map (Manifold.DolbeaultComparison.locallyConstantComplexHolomorphicSheafMap (E := E) (M := M)) 2
      (CategoryTheory.Sheaf.H.map (rationalConstantComplexSheafMap (TopCat.of M)) 2 a) = 0) :
    HolomorphicPeriod.rationalHolomorphicObstruction E M a = 0 := by
  change CategoryTheory.Sheaf.H.map (HolomorphicPeriod.holomorphicRationalPeriodSheafMap E M) 2 a = 0
  rw [holomorphicRationalPeriodSheafMap_factor_complex,
    CategoryTheory.Sheaf.H.map_comp_apply, CategoryTheory.Sheaf.H.map_comp_apply, ha, map_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexPeriod
