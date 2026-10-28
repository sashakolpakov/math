import OAI.ArithmeticGeometry.Descent.CMVariety.StableGraphScheme
import OAI.AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis
import OAI.AlgebraicGeometry.ComplexMultiplication.CommonCMField

/-! # Graph CM -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GraphCM.Abelian.CMGraph

noncomputable section

section

/-!
Construct the isolated graph chart for the full product of CM fields.
Finitely many elements of the rational CM algebra separate every
holomorphic-antiholomorphic pair of characters. Over a number field
containing all character values, the invariant-graph functor is represented
by the spectrum of that number field, including on nonreduced test schemes.

This is the arithmetic linear period chart. Identifying it with a chart of
the moduli of abelian schemes is not asserted in this file.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
  {H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (D : AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition H)

abbrev FieldProduct := ∀ i : Fin D.numberOfComponents, (D.component i).field
abbrev HolomorphicIndex := {j : D.EmbeddingIndex // D.embeddingSign j = true}
abbrev AntiholomorphicIndex := {j : D.EmbeddingIndex // D.embeddingSign j = false}
abbrev ParameterIndex := AntiholomorphicIndex D × HolomorphicIndex D

def character (j : D.EmbeddingIndex) (a : FieldProduct D) : ℂ := j.2 (a j.1)

/-- Different characters of the product algebra are separated by an actual
element of that algebra, also when the characters belong to different factors. -/
theorem characters_separated (j k : D.EmbeddingIndex) (hjk : j ≠ k) :
    ∃ a : FieldProduct D, character D j a ≠ character D k a := by
  rcases j with ⟨i, σ⟩
  rcases k with ⟨i', τ⟩
  by_cases h : i = i'
  · subst i'
    have hστ : σ ≠ τ := fun h => hjk (by subst τ; rfl)
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hστ
    refine ⟨Pi.single i a, ?_⟩
    simpa [character] using ha
  · refine ⟨Pi.single i 1, ?_⟩
    simp [character, Ne.symm h]

theorem opposite_indices_ne (q : AntiholomorphicIndex D) (p : HolomorphicIndex D) :
    q.val ≠ p.val := by
  intro h
  have hs := congrArg D.embeddingSign h
  rw [q.property, p.property] at hs
  cases hs

/-- One separating element for each matrix coordinate. There are only
finitely many such coordinates in the CM period problem. -/
def separatingElement (t : ParameterIndex D) : FieldProduct D :=
  Classical.choose (characters_separated D t.1.val t.2.val (opposite_indices_ne D t.1 t.2))

theorem separatingElement_spec (t : ParameterIndex D) :
    character D t.1.val (separatingElement D t) ≠
      character D t.2.val (separatingElement D t) :=
  Classical.choose_spec (characters_separated D t.1.val t.2.val
    (opposite_indices_ne D t.1 t.2))

variable (K : IntermediateField ℚ ℂ)
  (hK : ∀ i (σ : (D.component i).field →ₐ[ℚ] ℂ), σ.fieldRange ≤ K)

def arithmeticCharacter (j : D.EmbeddingIndex) (a : FieldProduct D) : K :=
  ⟨character D j a, hK j.1 j.2 ⟨a j.1, rfl⟩⟩

def sourceEigenvalue (t : ParameterIndex D) (p : HolomorphicIndex D) : K :=
  arithmeticCharacter D K hK p.val (separatingElement D t)

def targetEigenvalue (t : ParameterIndex D) (q : AntiholomorphicIndex D) : K :=
  arithmeticCharacter D K hK q.val (separatingElement D t)

theorem eigenvalues_separated (q : AntiholomorphicIndex D) (p : HolomorphicIndex D) :
    ∃ t : ParameterIndex D,
      targetEigenvalue D K hK t q ≠ sourceEigenvalue D K hK t p := by
  refine ⟨(q, p), ?_⟩
  intro heq
  exact separatingElement_spec D (q, p) (congrArg Subtype.val heq)

def graphFunctor : (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ Type :=
  StableGraphScheme.Abelian.StableGraph.functor (sourceEigenvalue D K hK) (targetEigenvalue D K hK)

/-- The explicit representing scheme for the enhanced linear period chart. -/
def graphRepresentation :
    (graphFunctor D K hK).RepresentableBy (StableGraphScheme.Abelian.StableGraph.scheme (K := K)) :=
  StableGraphScheme.Abelian.StableGraph.representation _ _ (eigenvalues_separated D K hK)

/-- A number field and a representing scheme are actually constructed,
using the common coefficient-field theorem and the CM character separation. -/
theorem exists_arithmetic_graph_scheme :
    ∃ (K : IntermediateField ℚ ℂ), NumberField K ∧
      ∃ (hK : ∀ i (σ : (D.component i).field →ₐ[ℚ] ℂ), σ.fieldRange ≤ K),
        Nonempty ((graphFunctor D K hK).RepresentableBy (StableGraphScheme.Abelian.StableGraph.scheme (K := K))) ∧
        ∀ x : (StableGraphScheme.Abelian.StableGraph.scheme (K := K)).left, IsOpen {x} := by
  obtain ⟨K, hnumber, _, _, hK⟩ := D.exists_common_galois_cm_field
  exact ⟨K, hnumber, hK, ⟨graphRepresentation D K hK⟩, StableGraphScheme.Abelian.StableGraph.scheme_point_isolated⟩

end

section

/-!
The product CM algebra acts on the actual rational space underlying the
given Hodge structure. Its scalar extension has the characters used by
the arithmetic graph scheme. In particular, the finitely many separating
operators are actual rational Hodge endomorphisms, not independently
chosen complex diagonal matrices.
-/

open scoped DirectSum TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
  {H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (D : AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition H)

local instance (i : Fin D.numberOfComponents) : NumberField (D.component i).field :=
  (D.component i).cm.numberField

/-- The product-field action transported through the given internal sum. -/
def rationalAction (a : FieldProduct D) : U →ₗ[ℚ] U :=
  D.linearEquiv.toLinearMap.comp
    ((DirectSum.lmap (fun i => AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism (D.component i).field (a i))).comp
      D.linearEquiv.symm.toLinearMap)

theorem rationalAction_component (a : FieldProduct D) (i : Fin D.numberOfComponents)
    (u : (D.component i).subspace) :
    rationalAction D a u = (a i • u : (D.component i).subspace) := by
  change D.linearEquiv
    ((DirectSum.lmap (fun j => AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism (D.component j).field (a j)))
      (D.linearEquiv.symm (u : U))) = _
  rw [show D.linearEquiv.symm (u : U) = DirectSum.lof ℚ _ _ i u from
    D.linearEquiv.symm_apply_eq.mpr (D.linearEquiv_lof i u).symm]
  rw [DirectSum.lmap_lof, D.linearEquiv_lof]
  rfl

theorem rationalAction_inclusion (a : FieldProduct D) (i : Fin D.numberOfComponents) :
    (rationalAction D a).comp (D.component i).subspace.subtype =
      (D.component i).subspace.subtype.comp
        (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism (D.component i).field (a i)) := by
  ext u
  exact rationalAction_component D a i u

/-- Scalar extension acts on an actual embedding vector by its character. -/
theorem rationalAction_embeddingBasis (a : FieldProduct D) (j : D.EmbeddingIndex) :
    (rationalAction D a).baseChange ℂ (D.embeddingBasis j) =
      character D j a • D.embeddingBasis j := by
  rcases j with ⟨i, σ⟩
  rw [D.embeddingBasis_apply]
  have hi := congrArg (fun f : (D.component i).subspace →ₗ[ℚ] U => f.baseChange ℂ)
    (rationalAction_inclusion D a i)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hi
  change (rationalAction D a).baseChange ℂ
      ((D.component i).subspace.subtype.baseChange ℂ (D.componentEmbeddingBasis i σ)) =
    character D ⟨i, σ⟩ a •
      (D.component i).subspace.subtype.baseChange ℂ (D.componentEmbeddingBasis i σ)
  rw [← LinearMap.comp_apply, hi, LinearMap.comp_apply]
  have hEigen : (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism (D.component i).field (a i)).baseChange ℂ
      (D.componentEmbeddingBasis i σ) =
        σ (a i) • D.componentEmbeddingBasis i σ :=
    (D.component i).cm.embeddingBasis_eigen (a i) σ
  rw [hEigen, map_smul]
  rfl

/-- The action preserves both of the given Hodge subspaces. -/
theorem rationalAction_preserves_sign (a : FieldProduct D) (s : Bool)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) (hx : x ∈ H.signSubspace s) :
    (rationalAction D a).baseChange ℂ x ∈ H.signSubspace s := by
  rw [D.signSubspace_eq_span_embeddingBasis s] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    rw [rationalAction_embeddingBasis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

theorem rationalAction_hodge (a : FieldProduct D) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (rationalAction D a) :=
  rationalAction_preserves_sign D a true

/-- Faithfulness is inherited from each actual rank-one field action. -/
theorem rationalAction_injective : Function.Injective (rationalAction D) := by
  intro a b hab
  funext i
  apply (D.component i).cm.scalarEndomorphism_injective
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  have he := LinearMap.congr_fun hab (u : U)
  change ((a i • u : (D.component i).subspace) : U) =
    ((b i • u : (D.component i).subspace) : U)
  simpa only [rationalAction_component] using he

/-- The finite enhancement needed for the graph chart consists of rational
endomorphisms of the original Hodge structure. -/
def separatingOperator (t : ParameterIndex D) : U →ₗ[ℚ] U :=
  rationalAction D (separatingElement D t)

theorem separatingOperator_hodge (t : ParameterIndex D) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (separatingOperator D t) := rationalAction_hodge D _

end

/-!
The invariant graph calculation in the original complexified Hodge space.
The graph is an actual linear subspace, formed using the embedding basis
of the supplied CM decomposition. Invariance under the finite tuple of
rational Hodge operators forces its graph matrix to be zero.

No claim about algebraic families or their period maps is assumed here.
-/

open scoped BigOperators Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
  {H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (D : AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition H)

abbrev GraphMatrix := Matrix (AntiholomorphicIndex D) (HolomorphicIndex D) ℂ

/-- The ordinary graph map in the actual CM embedding basis. -/
def graphMap (L : GraphMatrix D) :
    (HolomorphicIndex D → ℂ) →ₗ[ℂ] AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U :=
  (∑ p, (LinearMap.proj p).smulRight (D.embeddingBasis p.val)) +
    ∑ q, (∑ p, L q p • LinearMap.proj p).smulRight (D.embeddingBasis q.val)

theorem graphMap_apply (L : GraphMatrix D) (v : HolomorphicIndex D → ℂ) :
    graphMap D L v =
      (∑ p, v p • D.embeddingBasis p.val) +
        ∑ q, (∑ p, L q p * v p) • D.embeddingBasis q.val := by
  simp [graphMap]

theorem graphMap_source (L : GraphMatrix D) (v : HolomorphicIndex D → ℂ)
    (p : HolomorphicIndex D) :
    D.embeddingBasis.repr (graphMap D L v) p.val = v p := by
  rw [graphMap_apply]
  simp [opposite_indices_ne D, Finsupp.single_apply, Subtype.val_inj]

theorem graphMap_target (L : GraphMatrix D) (v : HolomorphicIndex D → ℂ)
    (q : AntiholomorphicIndex D) :
    D.embeddingBasis.repr (graphMap D L v) q.val = ∑ p, L q p * v p := by
  rw [graphMap_apply]
  have hne (p : HolomorphicIndex D) : p.val ≠ q.val := Ne.symm (opposite_indices_ne D q p)
  simp [hne, Finsupp.single_apply, Subtype.val_inj]

theorem rationalAction_coefficient (a : FieldProduct D) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U)
    (j : D.EmbeddingIndex) :
    D.embeddingBasis.repr ((rationalAction D a).baseChange ℂ x) j =
      character D j a * D.embeddingBasis.repr x j := by
  conv_lhs => rw [← D.embeddingBasis.sum_repr x]
  simp only [map_sum, map_smul, rationalAction_embeddingBasis]
  simp [Finsupp.single_apply, mul_comm]

/-- The graph regarded as a subspace of the original complexification. -/
def graphSubspace (L : GraphMatrix D) : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) :=
  (graphMap D L).range

/-- The zero graph is exactly the holomorphic subspace originally supplied. -/
theorem graphSubspace_zero : graphSubspace D 0 = H.holomorphic := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    have he : graphMap D 0 v = ∑ p, v p • D.embeddingBasis p.val := by
      simp [graphMap_apply]
    rw [he]
    apply Submodule.sum_mem
    intro p _
    exact Submodule.smul_mem _ _ (D.embeddingBasis_holomorphic p.val p.property)
  · rw [show H.holomorphic =
        Submodule.span ℂ (D.embeddingBasis '' {j | D.embeddingSign j = true}) from
      D.signSubspace_eq_span_embeddingBasis true]
    apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    refine ⟨Pi.single (⟨j, hj⟩ : HolomorphicIndex D) 1, ?_⟩
    simp [graphMap_apply, Pi.single_apply]

/-- Invariance is tested using the actual scalar extension of rational
endomorphisms of the original space. -/
def IsInvariantGraph (L : GraphMatrix D) : Prop :=
  ∀ t (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U), x ∈ graphSubspace D L →
    (separatingOperator D t).baseChange ℂ x ∈ graphSubspace D L

/-- Read the matrix equations from the invariance of the actual subspace. -/
theorem equations_of_invariant_graph (L : GraphMatrix D) (hL : IsInvariantGraph D L) :
    StableGraphScheme.Abelian.StableGraph.Equations
      (fun t p => character D p.val (separatingElement D t))
      (fun t q => character D q.val (separatingElement D t)) (RingHom.id ℂ) L := by
  intro t q p
  let v : HolomorphicIndex D → ℂ := Pi.single p 1
  obtain ⟨w, hw⟩ := hL t (graphMap D L v) ⟨v, rfl⟩
  have hwc (p' : HolomorphicIndex D) :
      w p' = character D p'.val (separatingElement D t) * v p' := by
    have he := congrArg (fun x => D.embeddingBasis.repr x p'.val) hw
    simpa only [separatingOperator, graphMap_source, rationalAction_coefficient] using he
  have he := congrArg (fun x => D.embeddingBasis.repr x q.val) hw
  simp only [separatingOperator, graphMap_target, rationalAction_coefficient] at he
  simp [hwc, v, Pi.single_apply] at he
  exact he.symm

/-- Every invariant graph through the CM period is the original graph. -/
theorem invariant_graph_matrix_zero (L : GraphMatrix D) (hL : IsInvariantGraph D L) :
    L = 0 := by
  apply StableGraphScheme.Abelian.StableGraph.matrix_eq_zero
    (fun t p => character D p.val (separatingElement D t))
    (fun t q => character D q.val (separatingElement D t))
    (fun q p => ⟨(q, p), separatingElement_spec D (q, p)⟩)
    (RingHom.id ℂ) ⟨L, equations_of_invariant_graph D L hL⟩

theorem invariant_graph_eq_holomorphic (L : GraphMatrix D) (hL : IsInvariantGraph D L) :
    graphSubspace D L = H.holomorphic := by
  rw [invariant_graph_matrix_zero D L hL, graphSubspace_zero]

theorem antiholomorphic_source_coefficient_zero (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U)
    (hx : x ∈ H.antiholomorphic) (p : HolomorphicIndex D) :
    D.embeddingBasis.repr x p.val = 0 := by
  by_contra hn
  have he := D.embeddingBasis_repr_sign (b := false) hx p.val hn
  rw [p.property] at he
  cases he

/-- Every complement of the antiholomorphic space is an actual graph in
the supplied embedding basis. No chart parametrization is postulated. -/
theorem exists_graph_of_complement (W : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U))
    (hW : IsCompl W H.antiholomorphic) :
    ∃ L : GraphMatrix D, graphSubspace D L = W := by
  let P := W.projection H.antiholomorphic hW
  let L : GraphMatrix D := fun q p => D.embeddingBasis.repr (P (D.embeddingBasis p.val)) q.val
  have hsource (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) (p : HolomorphicIndex D) :
      D.embeddingBasis.repr (P x) p.val = D.embeddingBasis.repr x p.val := by
    have he := antiholomorphic_source_coefficient_zero D (x - P x)
      (Submodule.sub_projection_mem hW x) p
    simp only [map_sub, Finsupp.sub_apply] at he
    exact (sub_eq_zero.mp he).symm
  have heq (v : HolomorphicIndex D → ℂ) :
      graphMap D L v = P (graphMap D 0 v) := by
    apply D.embeddingBasis.repr.injective
    ext j
    cases hj : D.embeddingSign j with
    | false =>
      have hl := graphMap_target D L v ⟨j, hj⟩
      rw [hl]
      have hzero : graphMap D 0 v = ∑ p, v p • D.embeddingBasis p.val := by
        simp [graphMap_apply]
      rw [hzero]
      simp [L, mul_comm]
    | true =>
      have hl := graphMap_source D L v ⟨j, hj⟩
      rw [hl, hsource _ ⟨j, hj⟩, graphMap_source D 0 v ⟨j, hj⟩]
  refine ⟨L, le_antisymm ?_ ?_⟩
  · rintro x ⟨v, rfl⟩
    rw [heq]
    exact Submodule.projection_apply_mem hW _
  · intro x hx
    let y := H.holomorphic.projection H.antiholomorphic H.complementary x
    have hy : y ∈ graphSubspace D 0 := by
      rw [graphSubspace_zero]
      exact Submodule.projection_apply_mem H.complementary x
    obtain ⟨v, hv⟩ := hy
    refine ⟨v, ?_⟩
    rw [heq, hv]
    have hz : P (x - y) = 0 :=
      Submodule.projection_apply_of_mem_right hW
        (Submodule.sub_projection_mem H.complementary x)
    rw [map_sub, Submodule.projection_apply_of_mem_left hW hx] at hz
    exact (sub_eq_zero.mp hz).symm

/-- The fixed CM period is the only invariant subspace in its entire
Grassmannian graph chart, expressed without a chosen graph matrix. -/
theorem invariant_complement_eq_holomorphic (W : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U))
    (hW : IsCompl W H.antiholomorphic)
    (hInv : ∀ t (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U), x ∈ W →
      (separatingOperator D t).baseChange ℂ x ∈ W) :
    W = H.holomorphic := by
  obtain ⟨L, rfl⟩ := exists_graph_of_complement D W hW
  exact invariant_graph_eq_holomorphic D L hInv

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GraphCM.Abelian.CMGraph
