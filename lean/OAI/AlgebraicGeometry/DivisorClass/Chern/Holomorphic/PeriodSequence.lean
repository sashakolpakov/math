import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves
import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralConstantSheaf
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.AB

/-! # Period Sequence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PeriodSequence

noncomputable section

/-! The actual integral-period map and holomorphic exponential sequence, exact on every section at the middle term. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def abelianSheafSections (X : TopCat.{0}) (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} where
  obj F := F.obj.obj (op U)
  map f := f.hom.app (op U)

instance abelianSheafSections_additive (X : TopCat.{0}) (U : Opens X) :
    (abelianSheafSections X U).Additive where
  map_add := rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicIntegralPeriod : LocallyConstant M ℤ →+ Exponential.HolomorphicFunction (E := E) (M := M) where
  toFun := Exponential.holomorphicPeriodFunction
  map_zero' := by
    apply ContMDiffMap.ext
    intro x
    simp [Exponential.holomorphicPeriodFunction]
  map_add' n m := by
    apply ContMDiffMap.ext
    intro x
    change ((n x + m x : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = _
    rw [Int.cast_add, add_mul]
    rfl

variable (E M)

def holomorphicPeriodSheafMap : IntegralConstantSheaf.integralConstantSheaf (TopCat.of M) ⟶ Holomorphic.Sheaves.holomorphicFunctionSheaf E M :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (holomorphicIntegralPeriod (E := E) (M := U.unop))
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      ext n
      apply ContMDiffMap.ext
      intro x
      rfl }

theorem holomorphicPeriodSheafMap_exponential :
    holomorphicPeriodSheafMap E M ≫ Holomorphic.Sheaves.holomorphicExponentialSheafMap E M = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  exact Exponential.exp_holomorphicPeriodFunction (E := E) n

def holomorphicExponentialSequence : ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of M)) :=
  ShortComplex.mk (holomorphicPeriodSheafMap E M) (Holomorphic.Sheaves.holomorphicExponentialSheafMap E M)
    (holomorphicPeriodSheafMap_exponential E M)

theorem holomorphicExponentialSequence_section_exact (U : Opens M) :
    ((holomorphicExponentialSequence E M).map
      (abelianSheafSections (TopCat.of M) U)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro g hg
  change Exponential.holomorphicExpUnit g = 1 at hg
  obtain ⟨n, hn⟩ := (Exponential.holomorphicExponential_kernel g).mp hg
  exact ⟨n, hn⟩

theorem holomorphicPeriodSheafMap_section_injective (U : Opens M) :
    Function.Injective ((holomorphicPeriodSheafMap E M).hom.app (op U)) :=
  Exponential.holomorphicPeriodFunction_injective

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PeriodSequence
