import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.Realizations

/-! # Discrete -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction

noncomputable section

section

/-! Discreteness of arithmetic matrix stabilizers in the full archimedean
product, by evaluation on finitely many spanning lattice vectors. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

variable {k : Type} [Field k] [NumberField k]

omit [NumberField k] in
@[fun_prop] theorem continuous_adele_to_mixed :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace k) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.property).continuous.comp
      (continuous_apply v.val)
  · apply continuous_pi
    intro v
    exact (InfinitePlace.Completion.isometry_extensionEmbedding v.val).continuous.comp
      (continuous_apply v.val)

variable {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)

def archimedeanEvaluate (g : G.ArchimedeanProduct Set.univ) (x : Fin n → k) :
    Fin n → mixedSpace k := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace k
      (fun v => ∑ j, (g ⟨v, Set.mem_univ v⟩).val i j * algebraMap k v.Completion (x j))

omit [NumberField k] in
theorem continuous_archimedeanEntry (v : InfinitePlace k) (i j : Fin n) :
    Continuous (fun g : G.ArchimedeanProduct Set.univ =>
      (g ⟨v, Set.mem_univ v⟩).val i j) := by
  have h0 : Continuous (fun g : G.ArchimedeanProduct Set.univ =>
      g ⟨v, Set.mem_univ v⟩) := continuous_apply _
  exact (continuous_apply j).comp
    (Matrix.SpecialLinearGroup.continuous_apply _ (continuous_subtype_val.comp h0) i)

omit [NumberField k] in
theorem continuous_archimedeanEvaluate (x : Fin n → k) :
    Continuous (fun g : G.ArchimedeanProduct Set.univ => archimedeanEvaluate G g x) := by
  apply continuous_pi
  intro i
  apply continuous_adele_to_mixed.comp
  change Continuous (fun g : G.ArchimedeanProduct Set.univ =>
    fun v : InfinitePlace k =>
      ∑ j, (g ⟨v, Set.mem_univ v⟩).val i j * algebraMap k v.Completion (x j))
  apply continuous_pi
  intro v
  apply continuous_finsetSum
  intro j _
  exact (continuous_archimedeanEntry G v i j).mul continuous_const

omit [NumberField k] in
theorem archimedeanEvaluate_diagonal (g : G.RationalPoints) (x : Fin n → k) :
    archimedeanEvaluate G (G.diagonal Set.univ g) x =
      IntegralLattice.Construction.vectorMixedEmbedding (k := k) n (G.representation g x) := by
  funext i
  change InfiniteAdeleRing.ringEquiv_mixedSpace k _ =
    mixedEmbedding k (G.representation g x i)
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  apply congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace k)
  funext v
  change (∑ j, algebraMap k v.Completion (g.val i j) * algebraMap k v.Completion (x j)) =
    algebraMap k v.Completion (∑ j, g.val i j * x j)
  simp only [map_sum, map_mul]

theorem vectorMixedEmbedding_injective (n : ℕ) :
    Function.Injective (IntegralLattice.Construction.vectorMixedEmbedding (k := k) n) := by
  intro x y he
  funext i
  exact mixedEmbedding_injective k (congrFun he i)

/-- Every full integral lattice stabilizer is discrete in the product of
all archimedean point groups. Semisimplicity is not needed for this part. -/
theorem full_diagonal_stabilizer_discrete (Λ : IntegralLattice.FullLattice k n) :
    DiscreteTopology ((G.latticeStabilizer Λ).map (G.diagonal Set.univ)) := by
  obtain ⟨s, hs⟩ := Λ.finite
  have hspan : Submodule.span k (s : Set (Fin n → k)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 k) k, hs, Λ.full]
  have hsΛ : ∀ x ∈ s, x ∈ Λ.module := by
    intro x hx
    rw [← hs]
    exact Submodule.subset_span hx
  let : DiscreteTopology (IntegralLattice.Construction.vectorLatticeImage Λ.module) :=
    IntegralLattice.Construction.vectorLatticeImage_discrete Λ.module Λ.finite
  let f : ((G.latticeStabilizer Λ).map (G.diagonal Set.univ)) →
      (s → IntegralLattice.Construction.vectorLatticeImage Λ.module) := fun a x =>
    ⟨archimedeanEvaluate G a.val x.val, by
      obtain ⟨g, hg, he⟩ := a.property
      rw [← he, archimedeanEvaluate_diagonal]
      apply (IntegralLattice.Construction.mem_vectorLatticeImage Λ.module _).mpr
      refine ⟨G.representation g x.val, ?_, rfl⟩
      exact ((G.mem_latticeStabilizer Λ g).mp hg x.val).mpr (hsΛ x.val x.property)⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro x
    exact ((continuous_archimedeanEvaluate G x.val).comp continuous_subtype_val).subtype_mk _
  · intro a b hab
    obtain ⟨g, hg, hga⟩ := a.property
    obtain ⟨h, hh, hhb⟩ := b.property
    have hgh : g = h := by
      apply G.representation_injective
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext_on hspan
      intro x hx
      have he := congrArg (fun F : s → IntegralLattice.Construction.vectorLatticeImage Λ.module => (F ⟨x, hx⟩).val) hab
      change archimedeanEvaluate G a.val x = archimedeanEvaluate G b.val x at he
      rw [← hga, ← hhb, archimedeanEvaluate_diagonal, archimedeanEvaluate_diagonal] at he
      exact vectorMixedEmbedding_injective n he
    apply Subtype.ext
    exact hga.symm.trans ((congrArg (G.diagonal Set.univ) hgh).trans hhb)

end

/-! Discreteness survives commensurability and omission of compact
archimedean factors. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

theorem discrete_map_of_closedMap
    {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [T2Space A]
    (f : A →* B) (hf : IsClosedMap f) (H : Subgroup A) [DiscreteTopology H] :
    DiscreteTopology (H.map f) := by
  let q : H → H.map f := fun x => ⟨f x.val, ⟨x.val, x.property, rfl⟩⟩
  have hq : Function.Surjective q := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc : IsClosedMap (fun x : H => f x.val) :=
    hf.comp Subgroup.isClosed_of_discreteTopology.isClosedMap_subtype_val
  apply discreteTopology_iff_forall_isClosed.mpr
  intro s
  have hs := (hc (q ⁻¹' s) (isClosed_discrete _)).preimage
    (continuous_subtype_val : Continuous (Subtype.val : H.map f → B))
  convert hs using 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := hq x
    exact ⟨y, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    have hxy : q y = x := Subtype.ext he
    exact hxy ▸ hy

theorem commensurable_map_of_injective
    {A B : Type*} [Group A] [Group B] {H J : Subgroup A}
    (h : H.Commensurable J) (f : A →* B) (hf : Function.Injective f) :
    (H.map f).Commensurable (J.map f) := by
  simpa only [Subgroup.Commensurable, Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero,
    Subgroup.relIndex_map_map_of_injective _ _ hf] using h

variable {k : Type} [Field k] [NumberField k] {n : ℕ}
variable (G : Algebraic.MatrixAlgebraicGroup k n)

def univProductHomeomorph :
    G.ArchimedeanProduct Set.univ ≃ₜ ((v : NumberField.InfinitePlace k) → G.AtPlace v) where
  toFun g v := g ⟨v, Set.mem_univ v⟩
  invFun g v := g v.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by apply continuous_pi; intro v; exact continuous_apply _
  continuous_invFun := continuous_pi fun v => continuous_apply v.val

def archimedeanProjection (S : Set (NumberField.InfinitePlace k)) :
    G.ArchimedeanProduct Set.univ →* G.ArchimedeanProduct S where
  toFun g v := g ⟨v.val, Set.mem_univ v.val⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField k] in
theorem archimedeanProjection_closed (S : Set (NumberField.InfinitePlace k))
    (hcompact : ∀ v, v ∉ S → CompactSpace (G.AtPlace v)) :
    IsClosedMap (archimedeanProjection G S) := by
  let : ∀ v : {v : NumberField.InfinitePlace k // v ∉ S},
      CompactSpace (G.AtPlace v.val) := fun v => hcompact v.val v.property
  let e := (univProductHomeomorph G).trans
    (Homeomorph.piEquivPiSubtypeProd (· ∈ S) (fun v => G.AtPlace v))
  have he : (archimedeanProjection G S : _ → _) = Prod.fst ∘ e := rfl
  rw [he]
  exact isClosedMap_fst_of_compactSpace.comp e.isClosedMap

omit [NumberField k] in
theorem projection_diagonal (S : Set (NumberField.InfinitePlace k)) :
    (archimedeanProjection G S).comp (G.diagonal Set.univ) = G.diagonal S := by
  apply MonoidHom.ext
  intro g
  funext v
  rfl

theorem full_diagonal_injective : Function.Injective (G.diagonal Set.univ) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace k))
  intro g h he
  apply G.map_injective (RingHom.id k) (algebraMap k v.Completion)
  exact congrFun he ⟨v, Set.mem_univ v⟩

/-- Arithmetic subgroups remain discrete after compact local factors are omitted. -/
theorem selected_diagonal_arithmetic_discrete
    (Λ : IntegralLattice.FullLattice k n) (Γ : Subgroup G.RationalPoints)
    (hΓ : Γ.Commensurable (G.latticeStabilizer Λ))
    (S : Set (NumberField.InfinitePlace k))
    (hcompact : ∀ v, v ∉ S → CompactSpace (G.AtPlace v)) :
    DiscreteTopology (Γ.map (G.diagonal S)) := by
  let : DiscreteTopology ((G.latticeStabilizer Λ).map (G.diagonal Set.univ)) :=
    full_diagonal_stabilizer_discrete G Λ
  have hcomm := commensurable_map_of_injective hΓ (G.diagonal Set.univ)
    (full_diagonal_injective G)
  let : DiscreteTopology (Γ.map (G.diagonal Set.univ)) := hcomm.discreteTopology_iff.mpr
    (full_diagonal_stabilizer_discrete G Λ)
  have hd := discrete_map_of_closedMap (archimedeanProjection G S)
    (archimedeanProjection_closed G S hcompact) (Γ.map (G.diagonal Set.univ))
  rw [Subgroup.map_map, projection_diagonal] at hd
  exact hd

theorem discrete_of_continuous_equiv_map
    {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ* B) (H : Subgroup A) [DiscreteTopology (H.map e.toMonoidHom)] :
    DiscreteTopology H := by
  let f : H → H.map e.toMonoidHom := fun x => ⟨e x.val, ⟨x.val, x.property, rfl⟩⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (e.continuous.comp continuous_subtype_val).subtype_mk _
  · intro x y he
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val he

/-- The discreteness assertion for the exact repaired Lattices interface. -/
theorem arithmetic_subgroup_discrete
    {Gk GInf : Type} [Group Gk] [Group GInf]
    [TopologicalSpace GInf] [IsTopologicalGroup GInf] [T2Space GInf]
    (D : Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf) (Γ₀ Γ : Subgroup Gk)
    (hmodel : IntegralLattice.IsArithmeticPresentation D δ Γ₀) (hΓ : Γ.Commensurable Γ₀) :
    DiscreteTopology (Γ.map δ) := by
  obtain ⟨Λ, r, S, e, hcompact, hΓ₀, hδ⟩ := hmodel
  have hcomm := commensurable_map_of_injective hΓ r.toMonoidHom r.injective
  rw [hΓ₀] at hcomm
  have hd := selected_diagonal_arithmetic_discrete D.matrixGroup Λ (Γ.map r.toMonoidHom)
    hcomm S hcompact
  have heq : (Γ.map δ).map e.toMonoidHom =
      (Γ.map r.toMonoidHom).map (D.matrixGroup.diagonal S) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    exact hδ
  let : DiscreteTopology ((Γ.map δ).map e.toMonoidHom) := heq.symm ▸ hd
  exact discrete_of_continuous_equiv_map e (Γ.map δ)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction
