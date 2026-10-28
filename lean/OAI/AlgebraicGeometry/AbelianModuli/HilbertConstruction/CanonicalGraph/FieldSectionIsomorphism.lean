import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FieldSectionIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.ResidueCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerBasis

/-! # Field Section Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every positive graph power over a Noetherian affine tame base commutes
with every field-valued base change on actual global sections. This includes
the fixed power used for the uniform field embedding. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_fieldSectionTensorComparison_bijective
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (m : ℕ) (hm : 0 < m)
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S) :
    Function.Bijective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison
      (IsPullback.of_hasPullback A.abelian.scheme.hom b)
        (A.graphBundle.tensorPower m).sheaf).app (op ⊤)) :=
  ProperFlat.FieldSectionIsomorphism.properFlat_fieldSectionTensorComparison_bijective A.abelian.scheme.hom (A.graphBundle.tensorPower m)
    (fun x => A.graphBundle_residueFiber_positivePower_cohomology_subsingleton hN hunit x m hm 0)
    (IsPullback.of_hasPullback A.abelian.scheme.hom b)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_fieldSectionTensorComparison_isIso
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (m : ℕ) (hm : 0 < m)
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S) :
    IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison (IsPullback.of_hasPullback A.abelian.scheme.hom b)
      (A.graphBundle.tensorPower m).sheaf).app (op ⊤)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (A.graphBundle_positivePower_fieldSectionTensorComparison_bijective hN hunit m hm b)

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_fieldSectionTensorComparison_isIso
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S) :
    IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison (IsPullback.of_hasPullback A.abelian.scheme.hom b)
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf).app (op ⊤)) :=
  A.graphBundle_positivePower_fieldSectionTensorComparison_isIso hN hunit
    (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
