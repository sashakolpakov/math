import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldDeRham
import OAI.AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel
import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedDerivativeProjection

/-! # Dolbeault Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultComparison

noncomputable section

/-! The actual coefficient and degree-zero/one maps from de Rham to Dolbeault sheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def locallyConstantComplexHolomorphic (U : Opens M) :
    LocallyConstant U ℂ →ₗ[ℂ] Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) where
  toFun f := ⟨f, fun x => contMDiffAt_const.congr_of_eventuallyEq (f.isLocallyConstant.eventually_eq x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def locallyConstantComplexHolomorphicSheafMap :
    Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf (TopCat.of M) ⟶ Holomorphic.Sheaves.holomorphicFunctionSheaf E M :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (locallyConstantComplexHolomorphic (E := E) U.unop).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      apply ContMDiffMap.ext
      intro x
      rfl }

def openManifoldZeroPure (U : Opens M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 →ₗ[ℂ] Open.ManifoldBidegree.AntiOpenManifoldForm E U 0 where
  toFun f := ⟨f, fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def manifoldZeroPureSheafMap : Abelian.ManifoldDeRham.abelianManifoldFormSheaf E M 0 ⟶ PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0 :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (openManifoldZeroPure (E := E) U.unop).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      rfl }

def manifoldOneAntiProjectionSheafMap : Abelian.ManifoldDeRham.abelianManifoldFormSheaf E M 1 ⟶ PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 1 :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (OneFormProjection.openManifoldOneAntiProjection (E := E) (U := U.unop)).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      exact (MixedDerivativeProjection.openManifoldOneAntiProjection_restrict (leOfHom i.unop) f).symm }

theorem manifoldDolbeaultComparison_zero_comm :
    locallyConstantComplexHolomorphicSheafMap (E := E) (M := M) ≫ ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf =
      Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M ≫ manifoldZeroPureSheafMap := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (locallyConstantComplexHolomorphic U.unop f) x v =
    Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm E U.unop f x v
  rw [Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply, Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm_apply]
  rfl

theorem manifoldDolbeaultComparison_one_comm :
    manifoldZeroPureSheafMap (E := E) (M := M) ≫ PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 0 =
      Abelian.ManifoldDeRham.abelianManifoldFormSheafD E M 0 ≫ manifoldOneAntiProjectionSheafMap := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact Subtype.ext (OneFormProjection.openManifoldOnePart_d f).symm

def manifoldDeRhamDolbeaultZeroComparison :
    Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M ⟶ ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence (E := E) (M := M) where
  τ₁ := locallyConstantComplexHolomorphicSheafMap
  τ₂ := manifoldZeroPureSheafMap
  τ₃ := manifoldOneAntiProjectionSheafMap
  comm₁₂ := manifoldDolbeaultComparison_zero_comm
  comm₂₃ := manifoldDolbeaultComparison_one_comm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultComparison
