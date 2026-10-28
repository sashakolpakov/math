import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts
import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultSheafMaps
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf
import Mathlib.Algebra.Homology.Single

/-! # Pure Manifold Dolbeault Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf

noncomputable section

/-! The actual pure Dolbeault sheaf complex on a complex manifold. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def antiOpenManifoldFormPresheaf (q : ℕ) : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of M) where
  obj U := ModuleCat.of ℂ (Open.ManifoldBidegree.AntiOpenManifoldForm E U.unop q)
  map h := ModuleCat.ofHom (Open.ManifoldBidegree.antiOpenManifoldFormRestrict (leOfHom h.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_refl form.1)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans (leOfHom f.unop) (leOfHom g.unop) form.1).symm

theorem antiOpenManifoldFormPresheaf_isSheaf (q : ℕ) :
    (antiOpenManifoldFormPresheaf E M q).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (antiOpenManifoldFormPresheaf E M q)).2
  intro ι U forms hcompat
  have hlocal : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.Compatible (fun i => (forms i).1) := by
    apply (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.compatible_iff_restrict _).2
    intro i j
    exact congrArg Subtype.val (hcompat i j)
  obtain ⟨form, hform, huniq⟩ := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.existsUnique_glue_iSup _ hlocal
  have hpure : Open.ManifoldBidegree.OpenManifoldHasBidegree 0 q form := by
    intro e he y hy
    obtain ⟨i, hi⟩ : ∃ i, e.symm y ∈ U i := by
      have hym : e.symm y ∈ (⨆ i, U i) := hy.2
      simpa only [Opens.mem_iSup] using hym
    have heq := congrArg (fun f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (U i) q => f.extension.inChart e y) (hform i)
    rw [Open.ManifoldBidegree.openManifold_restrict_inChart _ form e hi] at heq
    rw [heq]
    exact (forms i).2 e he y ⟨hy.1, hi⟩
  refine ⟨⟨form, hpure⟩, fun i => Subtype.ext (hform i), ?_⟩
  intro other hother
  apply Subtype.ext
  apply huniq other.1
  intro i
  exact congrArg Subtype.val (hother i)

def antiOpenManifoldFormSheaf (q : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) where
  obj := antiOpenManifoldFormPresheaf E M q
  property := antiOpenManifoldFormPresheaf_isSheaf E M q

def abelianAntiOpenManifoldFormSheaf (q : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of M))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (antiOpenManifoldFormSheaf E M q)

def pureManifoldDolbeaultSheafMap (q : ℕ) :
    abelianAntiOpenManifoldFormSheaf E M q ⟶ abelianAntiOpenManifoldFormSheaf E M (q + 1) :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD U.unop q).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro form
      exact (Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD_restrict (leOfHom i.unop) form).symm }

theorem pureManifoldDolbeaultSheafMap_squared (q : ℕ) :
    pureManifoldDolbeaultSheafMap E M q ≫ pureManifoldDolbeaultSheafMap E M (q + 1) = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro form
  exact Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD_squared U.unop q form

def pureManifoldDolbeaultSheafComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) ℕ :=
  CochainComplex.of (abelianAntiOpenManifoldFormSheaf E M) (pureManifoldDolbeaultSheafMap E M)
    (pureManifoldDolbeaultSheafMap_squared E M)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf
