import OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel
import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultSheafZeroExact

/-! # Manifold Dolbeault Zero Kernel -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel

noncomputable section

/-! The original holomorphic sheaf is precisely the zero-degree kernel in the pure Dolbeault complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def pureHolomorphicManifoldZeroFormLinear (U : Opens M) :
    Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) →ₗ[ℂ] Open.ManifoldBidegree.AntiOpenManifoldForm E U 0 where
  toFun g := ⟨Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroFormLinear U g, fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _⟩
  map_add' f g := Subtype.ext ((Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroFormLinear U).map_add f g)
  map_smul' c f := Subtype.ext ((Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroFormLinear U).map_smul c f)

theorem pureHolomorphicManifoldZeroFormLinear_injective (U : Opens M) :
    Function.Injective (pureHolomorphicManifoldZeroFormLinear (E := E) U) := by
  intro f g h
  exact Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroFormLinear_injective U (congrArg Subtype.val h)

theorem pureHolomorphicManifoldZeroFormLinear_d (U : Opens M) (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD U 0 (pureHolomorphicManifoldZeroFormLinear U g) = 0 :=
  Subtype.ext (Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_d g)

def holomorphicToPureManifoldZeroFormSheaf :
    Holomorphic.Sheaves.holomorphicFunctionSheaf E M ⟶ PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0 :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (pureHolomorphicManifoldZeroFormLinear U.unop).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro g
      apply Subtype.ext
      exact (Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_restrict (leOfHom i.unop) g
        ((Holomorphic.Sheaves.holomorphicFunctionSheaf E M).obj.map i g) (fun _ => rfl)).symm }

theorem holomorphicToPureManifoldZeroFormSheaf_mono : Mono (holomorphicToPureManifoldZeroFormSheaf (E := E) (M := M)) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mpr (pureHolomorphicManifoldZeroFormLinear_injective U.unop)

theorem holomorphicToPureManifoldZeroFormSheaf_d :
    holomorphicToPureManifoldZeroFormSheaf (E := E) (M := M) ≫ PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 0 = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro g
  exact pureHolomorphicManifoldZeroFormLinear_d U.unop g

def pureHolomorphicManifoldDolbeaultZeroSequence :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  ShortComplex.mk holomorphicToPureManifoldZeroFormSheaf (PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 0)
    holomorphicToPureManifoldZeroFormSheaf_d

variable [FiniteDimensional ℂ E]

theorem pureHolomorphicManifoldZeroFormLinear_range (U : Opens M) :
    LinearMap.range (pureHolomorphicManifoldZeroFormLinear (E := E) U) = LinearMap.ker (Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD U 0) := by
  ext form
  constructor
  · rintro ⟨g, rfl⟩
    exact pureHolomorphicManifoldZeroFormLinear_d U g
  · intro h
    have hz : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 form.1 = 0 := congrArg Subtype.val h
    have hr : form.1 ∈ LinearMap.range (Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroFormLinear U) := by
      rw [Manifold.DolbeaultZeroKernel.holomorphicManifoldZeroFormLinear_range]
      exact hz
    obtain ⟨g, hg⟩ := hr
    exact ⟨g, Subtype.ext hg⟩

theorem pureHolomorphicManifoldDolbeaultZeroSequence_section_exact (U : Opens M) :
    ((pureHolomorphicManifoldDolbeaultZeroSequence (E := E) (M := M)).map
      (Holomorphic.PeriodSequence.abelianSheafSections (TopCat.of M) U)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro form hform
  change Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD U 0 form = 0 at hform
  have h : form ∈ LinearMap.range (pureHolomorphicManifoldZeroFormLinear (E := E) U) := by
    rw [pureHolomorphicManifoldZeroFormLinear_range]
    exact hform
  exact h

theorem pureHolomorphicManifoldDolbeaultZeroSequence_exact :
    (pureHolomorphicManifoldDolbeaultZeroSequence (E := E) (M := M)).Exact :=
  Abelian.SheafLocalExact.abelianSheaf_exact_of_section_exact (TopCat.of M) _ pureHolomorphicManifoldDolbeaultZeroSequence_section_exact

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel
