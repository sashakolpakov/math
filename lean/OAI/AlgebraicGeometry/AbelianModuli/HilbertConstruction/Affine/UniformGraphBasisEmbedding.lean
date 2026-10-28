import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisEmbeddingFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.UniformGraphPowerGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldSectionIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerEmbedding

/-! # Uniform Graph Basis Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a Noetherian affine spectrum, any complete section basis of the
fixed graph power gives an actual relative closed embedding. The field
factorization and section-comparison hypotheses are discharged for graph bundles. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] [IsNoetherianRing Γ(Spec (.of R), ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))

include hg hδ hN hunit in
omit [IsNoetherianRing Γ(Spec (.of R), ⊤)] in
theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_field_consecutive_sections_factor
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ Spec (.of R)) (m : ℕ) (hm : 0 < m) :
    Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule (CategoryTheory.Limits.pullback A.abelian.scheme.hom b))
      ((((A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).pullback
        (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom b)).tensorPower m).sheaf)
      ((((A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).pullback
        (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom b)).tensorPower (1 + m)).sheaf) := by
  let B := A.pullback b
  let a := CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom b
  let d := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  let e : ((A.graphBundle.tensorPower d).pullback a).sheaf ≅ (B.graphBundle.tensorPower d).sheaf :=
    A.graphBundle.powerBaseChangeIso a d ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left d).mapIso (A.graphBundle_baseChangeIso b).symm
  have h : Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule B.abelian.scheme.left)
      ((B.graphBundle.tensorPower d).tensorPower m).sheaf
      ((B.graphBundle.tensorPower d).tensorPower (1 + m)).sheaf := by
    simpa only [d, Graph.EmbeddingNumerics.graphUniformEmbeddingDegree, Nat.add_comm 1 m] using
      B.graphBundle_uniform_power_consecutive_sections_factor hg hδ hN
        (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit b) m hm
  exact (h.sourceIso ((TensorPower.Maps.tensorPowerFunctor _ m).mapIso e).symm).targetIso
    ((TensorPower.Maps.tensorPowerFunctor _ (1 + m)).mapIso e).symm

include hδ hN hunit in
theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_coefficientBasis_covers {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) Γ(Spec (.of R), ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor A.abelian.scheme.hom.appTop.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf)) :
    ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf B i) :=
  Coefficient.RingSectionBasis.coefficientRingBasisFamily_covers A.abelian.scheme.hom.appTop.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)) B
    (A.uniformGraphPower_pointwise_sections_noetherian_affine hδ hN hunit)

include hg hδ hN hunit in
theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_coefficientBasis_closedImmersion {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) Γ(Spec (.of R), ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor A.abelian.scheme.hom.appTop.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf B i)) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf B) hs).left := by
  let L := A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  let s := Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom L.sheaf B
  have : IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left := by
    apply GeometricallyAmpleSectionMorphism.sectionProjectiveMorphism_isFinite_of_geometric_ample A.abelian.scheme.hom L s hs
    intro K _ _ b
    exact ((A.graphBundle_ample_geometricFiber K b).tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)).of_iso
        (A.graphBundle.powerBaseChangeIso (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom b)
          (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).symm
  exact Affine.BasisEmbeddingFieldCriterion.affine_basis_sectionMap_closedImmersion_of_field_factorizations A.abelian.scheme.hom L B hs
    (fun K _ b => A.graphBundle_positivePower_fieldSectionTensorComparison_bijective hN hunit
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) b)
    (fun K _ b m hm => A.uniformGraphPower_field_consecutive_sections_factor hg hδ hN hunit b m hm)

def PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerEmbeddingOfCoefficientBasis
    (B : Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1)) Γ(Spec (.of R), ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor A.abelian.scheme.hom.appTop.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf)) :
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom where
  degree := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  degree_pos := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ
  power := A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  isPower := A.graphBundle.tensorPower_isTensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  dimension := Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1
  sections := Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf B
  covers := A.uniformGraphPower_coefficientBasis_covers hδ hN hunit B
  closedImmersion := A.uniformGraphPower_coefficientBasis_closedImmersion hg hδ hN hunit B
    (A.uniformGraphPower_coefficientBasis_covers hδ hN hunit B)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
