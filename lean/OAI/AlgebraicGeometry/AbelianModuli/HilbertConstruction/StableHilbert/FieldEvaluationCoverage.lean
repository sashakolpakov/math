import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BasisCoordinateFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SparseCoverage

/-! # Field Evaluation Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The vectors obtained from the actual torsion evaluations satisfy the
strict subspace inequalities used by the stable balanced frame charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

omit [IsAlgClosed K] [NeZero n] in
theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelSectionEvaluation_ne_zero
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n) (i : Multiplicative (Fin (2 * g) → ZMod n)) :
    A.fullLevelSectionEvaluation level i ≠ 0 := by
  let L := A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  let x := ((A.abelian.fullLevelRationalTorsionEquiv level).symm i).val
  obtain ⟨s, hs⟩ := A.uniformGraphPower_pointwise_sections hδ hN hNk
    (x.left (IsLocalRing.closedPoint K))
  let v := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) L.sheaf s
  intro h
  have hz : A.fullLevelSectionEvaluation level i v = 0 := by rw [h]; rfl
  have he := (Rational.LineBundleEvaluation.rationalLineBundleEvaluation_eq_zero A.abelian.scheme.hom L x.left x.w v).mp hz
  have hv : (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
      L.sheaf).symm v = s := AddEquiv.symm_apply_apply _ _
  rw [hv] at he
  exact he hs

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelSectionEvaluation_sparse
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    (U : Submodule K (Module.Dual K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf)))
    (hU : U ≠ ⊤) :
    Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ *
      (Finset.univ.filter (fun i => A.fullLevelSectionEvaluation level i ∈ U)).card <
        Fintype.card (Multiplicative (Fin (2 * g) → ZMod n)) := by
  let L := A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  let V := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj L.sheaf
  let : Module.Finite K V :=
    A.graphBundle_positivePower_sections_finite_overField (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  have hr : Module.finrank K V = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ :=
    A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)
  have hs : ∀ v : V, v ≠ 0 → Module.finrank K V *
      (Finset.univ.filter (fun i => A.fullLevelSectionEvaluation level i v = 0)).card <
        Fintype.card (Multiplicative (Fin (2 * g) → ZMod n)) := by
    intro v hv
    let a := (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) L.sheaf).symm v
    have ha : a ≠ 0 := by
      intro h
      apply hv
      exact (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv
        (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) L.sheaf).symm.injective
          (h.trans (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv
            (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) L.sheaf).symm.map_zero.symm)
    have h := A.uniformGraphPower_fullLevel_hyperplanes_sparse hg hδ hN hNk level hlarge a ha
    have heq (i : Multiplicative (Fin (2 * g) → ZMod n)) :
        A.fullLevelSectionEvaluation level i v = 0 ↔
          A.abelian.fullLevelGeometricPoint level i ∉ Ample.LineBundles.sectionNonvanishing a :=
      Rational.LineBundleEvaluation.rationalLineBundleEvaluation_eq_zero A.abelian.scheme.hom L
        ((A.abelian.fullLevelRationalTorsionEquiv level).symm i).val.left
        ((A.abelian.fullLevelRationalTorsionEquiv level).symm i).val.w v
    simpa only [hr, heq, show Fintype.card (Multiplicative (Fin (2 * g) → ZMod n)) =
      n ^ (2 * g) by simp] using h
  have hsparse : Module.finrank K (Module.Dual K V) *
      (Finset.univ.filter (fun i => A.fullLevelSectionEvaluation level i ∈ U)).card <
        Fintype.card (Multiplicative (Fin (2 * g) → ZMod n)) :=
    SparseDualEvaluationFrames.dualEvaluation_family_sparse (A.fullLevelSectionEvaluation level) hs U hU
  simpa only [Subspace.dual_finrank_eq, hr] using hsparse

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelBasisCoordinates_enumerated_sparse
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    (b : Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)) K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf))
    (U : Submodule K (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) → K)) (hU : U ≠ ⊤) :
    Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * (Finset.univ.filter
      (fun i : Fin (n ^ (2 * g)) =>
        (fun k => A.fullLevelSectionEvaluation level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k)) ∈ U)).card <
      n ^ (2 * g) := by
  have hs := StableHilbert.SparseCoverage.StableHilbertCoverage.sparse_linearEquiv _ _
    (A.fullLevelSectionEvaluation_sparse hg hδ hN hNk level hlarge) b.dualBasis.equivFun
  have he := StableHilbert.SparseCoverage.StableHilbertCoverage.sparse_reindex _ _ hs
    (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := n)) U hU
  have hcoords (z : Fin (n ^ (2 * g))) :
      b.dualBasis.equivFun (A.fullLevelSectionEvaluation level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z)) =
        fun k => A.fullLevelSectionEvaluation level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) (b k) := by
    funext k
    exact b.dualBasis_equivFun _ k
  simpa only [hcoords, Fintype.card_fin] using he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
