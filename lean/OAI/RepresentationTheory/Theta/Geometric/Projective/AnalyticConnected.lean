import OAI.RepresentationTheory.Theta.Geometric.Projective.SubsetCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSubscheme
import Mathlib.Topology.Connected.Clopen

/-! # Analytic Connected -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.AnalyticConnected

noncomputable section

section

/-! A clopen analytic subset of an actual smooth integral projective
variety is cut out by a closed subset of its original scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions

variable (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Set X.analyticSpace)

theorem projectiveClopen_projective_equations (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ (Q : Finset (MvPolynomial (IntrinsicEmbedding.ProjectiveAmbientCoordinates X) ℂ)) (degree : Q → ℕ)
      (hQ : ∀ q : Q, q.val.IsHomogeneous (degree q)),
      IntrinsicEmbedding.projectiveNativeEmbedding X '' U = AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus (fun q : Q => q.val) degree hQ := by
  obtain ⟨Q, hQ, hcone⟩ := SubsetCone.projectiveSubsetCone_homogeneous_equations X U hU hne
  choose degree hdegree using fun q : Q => hQ q.val q.property
  refine ⟨Q, degree, hdegree, ?_⟩
  ext p
  have heq : p.rep ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (IntrinsicEmbedding.projectiveNativeEmbedding X '' U) ↔
      ∀ q ∈ Q, MvPolynomial.eval p.rep q = 0 := by
    change p.rep ∈ SubsetCone.projectiveSubsetCone X U ↔ _
    rw [hcone]
    rfl
  rw [AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff _ p.rep p.rep_nonzero, p.mk_rep] at heq
  rw [← p.mk_rep, AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus.mem_projectiveCommonZeroLocus_mk]
  simpa only [p.mk_rep, Subtype.forall] using heq

theorem projectiveClopen_exists_closed_support (hU : IsClopen U) :
    ∃ Z : Set X.toOver.left, IsClosed Z ∧
      ∀ x : X.analyticSpace, x ∈ U ↔ x.left (⊥ : PrimeSpectrum ℂ) ∈ Z := by
  by_cases hne : U.Nonempty
  · obtain ⟨Q, degree, hQ, hzero⟩ := projectiveClopen_projective_equations X U hU hne
    obtain ⟨Y, i, _, hi, _, himage⟩ :=
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSubscheme.Constructions.Algebraization.exists_reduced_projective_subscheme_of_equations (fun q : Q => q.val) degree hQ
    let : IsClosedImmersion i.left := hi
    let P := X.presentation.projective
    refine ⟨P.toOverHom.left ⁻¹' range i.left,
      i.left.isClosedEmbedding.isClosed_range.preimage P.toOverHom.left.continuous, ?_⟩
    intro x
    have hx : IntrinsicEmbedding.projectiveNativeEmbedding X x ∈ IntrinsicEmbedding.projectiveNativeEmbedding X '' U ↔ x ∈ U :=
      (IntrinsicEmbedding.projectiveNativeEmbedding_isClosedEmbedding X).injective.mem_set_image
    rw [hzero] at hx
    rw [← hx, ← himage]
    have he : AlgebraicGeometry.Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv P.ambientDimension (IntrinsicEmbedding.projectiveNativeEmbedding X x) =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.toOverHom x :=
      (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph P.ambientDimension).apply_symm_apply _
    rw [he]
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.toOverHom x ∈ range (fun q => q ≫ i) ↔ _
    rw [AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints.range_closedImmersion_complexPointMap]
    rfl
  · refine ⟨∅, isClosed_empty, ?_⟩
    intro x
    simp only [not_nonempty_iff_eq_empty.mp hne, mem_empty_iff_false]

end

/-! Analytic connectedness of actual smooth integral projective varieties,
proved from homogeneous equations and the irreducibility of their schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

variable (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance connectedProjectiveIntegral : IsIntegral X.toOver.left := X.property
local instance connectedProjectiveSmooth : Smooth X.toOver.hom := X.presentation.smooth

theorem projective_closed_support_eq_univ (Z : Set X.toOver.left) (hZ : IsClosed Z)
    (hpoints : ∀ x : X.analyticSpace, x.left (⊥ : PrimeSpectrum ℂ) ∈ Z) : Z = univ := by
  let : JacobsonSpace X.toOver.left := LocallyOfFiniteType.jacobsonSpace X.toOver.hom
  have hclosed : closedPoints X.toOver.left ⊆ Z := by
    intro z hz
    let p : X.analyticSpace := Over.homMk (pointOfClosedPoint X.toOver.hom z hz)
      (pointOfClosedPoint_comp X.toOver.hom z hz)
    have hp : p.left (⊥ : PrimeSpectrum ℂ) = z :=
      pointOfClosedPoint_apply X.toOver.hom z hz _
    simpa only [hp] using hpoints p
  apply univ_subset_iff.mp
  rw [← closure_closedPoints]
  exact hZ.closure_subset_iff.mpr hclosed

theorem projective_analytic_clopen_trivial (U : Set X.analyticSpace) (hU : IsClopen U) :
    U = ∅ ∨ U = univ := by
  obtain ⟨Z, hZ, hZU⟩ := projectiveClopen_exists_closed_support X U hU
  obtain ⟨W, hW, hWU⟩ := projectiveClopen_exists_closed_support X Uᶜ hU.compl
  have hcover : Z ∪ W = univ := projective_closed_support_eq_univ X (Z ∪ W) (hZ.union hW) (by
    intro x
    by_cases hx : x ∈ U
    · exact Or.inl ((hZU x).mp hx)
    · exact Or.inr ((hWU x).mp hx))
  have hirr : IsPreirreducible (univ : Set X.toOver.left) := PreirreducibleSpace.isPreirreducible_univ
  obtain h | h := isPreirreducible_iff_isClosed_union_isClosed.mp hirr Z W hZ hW (by rw [hcover])
  · right
    exact eq_univ_iff_forall.mpr fun x => (hZU x).mpr (h (mem_univ _))
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hWU x).mpr (h (mem_univ _)) hx

theorem projective_analytic_connected : ConnectedSpace X.analyticSpace :=
  connectedSpace_iff_clopen.mpr ⟨X.complexPoints_nonempty, projective_analytic_clopen_trivial X⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.AnalyticConnected
