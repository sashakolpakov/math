import Mathlib
import Lean.Util.CollectAxioms

/-! # Tensor Decomposition -/

namespace OAI.Analysis.Schwartz.TensorDecomposition.Constructions

noncomputable section

/-!
TensorDecomposition: finite tensor decompositions of locally constant, compactly supported
complex functions. This file does not import the statement placeholders.
-/

open Set _root_.Topology
open scoped BigOperators Classical

abbrev SchwartzBruhat (X : Type*) [TopologicalSpace X] :=
  { f : X → ℂ // IsLocallyConstant f ∧ HasCompactSupport f }

def char {X : Type*} (U : Set X) : X → ℂ :=
  U.indicator 1

@[simp] lemma char_mem {X : Type*} {U : Set X} {x : X} (h : x ∈ U) :
    char U x = 1 := by simp [char, h]

@[simp] lemma char_not_mem {X : Type*} {U : Set X} {x : X} (h : x ∉ U) :
    char U x = 0 := by simp [char, h]

@[simp] lemma char_empty {X : Type*} : char (∅ : Set X) = 0 := by
  ext x
  simp [char]

lemma compact_open_nhds {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ C : Set X, IsCompact C ∧ IsClopen C ∧ x ∈ C ∧ C ⊆ U := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCK⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
      (isOpen_interior.mem_nhds hxK)
  exact ⟨C, hK.of_isClosed_subset hC.isClosed (hCK.trans interior_subset),
    hC, hxC, hCK.trans (interior_subset.trans hKU)⟩

def charSB {X : Type*} [TopologicalSpace X] [T2Space X]
    (U : Set X) (hc : IsCompact U) (ho : IsClopen U) : SchwartzBruhat X :=
  ⟨char U, by
    simpa [char, LocallyConstant.coe_charFn] using
      (LocallyConstant.charFn ℂ ho).isLocallyConstant,
    by
      apply HasCompactSupport.intro hc
      intro x hx
      simp [char, hx]⟩

lemma span_mul_closed {X : Type*} (G : Set (X → ℂ))
    (hG : ∀ f ∈ G, ∀ g ∈ G, f * g ∈ G) :
    ∀ f ∈ Submodule.span ℂ G, ∀ g ∈ Submodule.span ℂ G,
      f * g ∈ Submodule.span ℂ G := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span (hG f hf g hg)
    | zero => simp
    | add g h hg hh ig ih => simpa [mul_add] using (Submodule.span ℂ G).add_mem ig ih
    | smul c g hg ig => simpa [mul_smul_comm] using (Submodule.span ℂ G).smul_mem c ig
  | zero => intro g hg; simp
  | add f h hf hh ih ik =>
    intro g hg
    simpa [add_mul] using (Submodule.span ℂ G).add_mem (ih g hg) (ik g hg)
  | smul c f hf ih =>
    intro g hg
    simpa [smul_mul_assoc] using (Submodule.span ℂ G).smul_mem c (ih g hg)

lemma compact_locally_constant_mem {X : Type*} [TopologicalSpace X]
    (M : Submodule ℂ (X → ℂ))
    (hM : ∀ f ∈ M, ∀ g ∈ M, f * g ∈ M)
    (f : X → ℂ) (hc : HasCompactSupport f)
    (hl : ∀ x ∈ tsupport f, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ char U ∈ M ∧ ∀ y ∈ U, f y = f x) :
    f ∈ M := by
  choose U hU hxU hmU hfU using fun x : tsupport f => hl x.1 x.2
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hi (t : Finset (tsupport f)) : f * char (⋃ a ∈ t, U a) ∈ M := by
    induction t using Finset.induction_on with
    | empty =>
      have he : (⋃ a ∈ (∅ : Finset (tsupport f)), U a) = ∅ := by simp
      rw [he, char_empty, mul_zero]
      exact M.zero_mem
    | @insert a t ha ih =>
      have heq : f * char (⋃ b ∈ insert a t, U b) =
          f a • char (U a) + f * char (⋃ b ∈ t, U b) -
            (f * char (⋃ b ∈ t, U b)) * char (U a) := by
        funext x
        have hset : (⋃ b ∈ insert a t, U b) = U a ∪ ⋃ b ∈ t, U b := by
          ext y
          simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
          aesop
        rw [hset]
        change f x * char _ x = f a * char _ x + f x * char _ x -
          (f x * char _ x) * char _ x
        by_cases hx : x ∈ U a
        · rw [char_mem (Set.mem_union_left _ hx), char_mem hx, hfU a x hx]
          ring
        · by_cases ht : x ∈ ⋃ b ∈ t, U b
          · rw [char_mem (Set.mem_union_right _ ht), char_not_mem hx, char_mem ht]
            ring
          · rw [char_not_mem (by simpa using And.intro hx ht), char_not_mem hx,
              char_not_mem ht]
            ring
      rw [heq]
      exact M.sub_mem (M.add_mem (M.smul_mem (f a) (hmU a)) ih)
        (hM _ ih _ (hmU a))
  have heq : f * char (⋃ a ∈ s, U a) = f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · change f x * char _ x = f x
      rw [char_mem (hs hx), mul_one]
    · change f x * char _ x = f x
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [← heq]
  exact hi s

def tensor {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)]
    (ψ : (i : ι) → SchwartzBruhat (X i)) : ((i : ι) → X i) → ℂ :=
  fun x => ∏ i, (ψ i).1 (x i)

lemma tensor_mul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)]
    (ψ η : (i : ι) → SchwartzBruhat (X i)) :
    tensor ψ * tensor η = tensor (fun i =>
      ⟨(ψ i).1 * (η i).1, (ψ i).2.1.mul (η i).2.1, (ψ i).2.2.mul_right⟩) := by
  funext x
  simp [tensor, Finset.prod_mul_distrib]

lemma finite_product_mem_span
    {ι : Type*} [Fintype ι] (X : ι → Type*)
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
    [∀ i, LocallyCompactSpace (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
    (φ : SchwartzBruhat ((i : ι) → X i)) :
    φ.1 ∈ Submodule.span ℂ (Set.range (tensor (X := X))) := by
  refine compact_locally_constant_mem _ ?_ φ.1 φ.2.2 ?_
  · apply span_mul_closed
    rintro _ ⟨ψ, rfl⟩ _ ⟨η, rfl⟩
    exact ⟨_, (tensor_mul ψ η).symm⟩
  intro x _
  obtain ⟨u, hu, huf⟩ := isOpen_pi_iff'.mp (φ.2.1.isOpen_fiber (φ.1 x)) x rfl
  choose C hc ho hx hCu using fun i => compact_open_nhds (hu i).1 (hu i).2
  refine ⟨Set.univ.pi C, isOpen_set_pi Set.finite_univ (fun i _ => (ho i).isOpen),
    (by simpa using hx), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨fun i => charSB (C i) (hc i) (ho i), ?_⟩
    funext y
    by_cases hy : ∀ i, y i ∈ C i
    · simp [tensor, charSB, char, hy]
    · obtain ⟨i, hi⟩ := not_forall.mp hy
      have hp : (∏ j, (charSB (C j) (hc j) (ho j)).1 (y j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [charSB, char, hi])
      change tensor _ y = char (Set.univ.pi C) y
      have hn : y ∉ Set.univ.pi C := fun h => hi (h i (Set.mem_univ i))
      rw [char_not_mem hn]
      exact hp
  · intro y hy
    exact huf (fun i hi => hCu i (hy i hi))

/-- The finite-product statement, with the hypotheses of the specification. -/
theorem finite_product_decomposition
    {ι : Type*} [Fintype ι]
    (X : ι → Type*)
    [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)]
    [∀ i, LocallyCompactSpace (X i)]
    [∀ i, TotallyDisconnectedSpace (X i)]
    (φ : SchwartzBruhat ((i : ι) → X i)) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (ψ : Fin n → (i : ι) → SchwartzBruhat (X i)),
      ∀ x : (i : ι) → X i,
        φ.1 x = ∑ j : Fin n, c j * ∏ i : ι, (ψ j i).1 (x i) := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (finite_product_mem_span X φ)
  let e := (Fintype.equivFin c.support).symm
  refine ⟨Fintype.card c.support, fun j => c (e j), fun j => (e j).1, ?_⟩
  intro x
  have hx := congrFun hc x
  have hx' : (∑ ψ ∈ c.support, c ψ * tensor ψ x) = φ.1 x := by
    simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx
  calc
    φ.1 x = ∑ ψ : c.support, c ψ * tensor ψ.1 x := by
      exact hx'.symm.trans
        (Finset.sum_coe_sort c.support (fun ψ => c ψ * tensor ψ x)).symm
    _ = ∑ j : Fin (Fintype.card c.support), c (e j) * tensor (e j).1 x :=
      (e.sum_comp (fun ψ : c.support => c ψ * tensor ψ.1 x)).symm

/-- A compactly supported locally constant function on a subspace of a product
is determined by finitely many of the ambient coordinates. -/
lemma finite_coordinates_control
    {ν : Type*} [DecidableEq ν] {V : ν → Type*}
    [∀ v, TopologicalSpace (V v)]
    {Y : Type*} [TopologicalSpace Y]
    (e : Y → (v : ν) → V v) (he : IsEmbedding e)
    (f : Y → ℂ) (hl : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ S : Finset ν, ∀ x y : Y,
      (∀ v ∈ S, e x v = e y v) → f x = f y := by
  have hloc (x : tsupport f) :
      ∃ (S : Finset ν) (u : (v : ν) → Set (V v)),
        IsOpen (e ⁻¹' (S : Set ν).pi u) ∧
        e x ∈ (S : Set ν).pi u ∧
        ∀ y : Y, e y ∈ (S : Set ν).pi u → f y = f x := by
    obtain ⟨W, hW, heW⟩ := he.isInducing.isOpen_iff.mp (hl.isOpen_fiber (f x))
    have hxW : e x ∈ W := by
      change x.1 ∈ e ⁻¹' W
      rw [heW]
      rfl
    obtain ⟨S, u, hu, hsub⟩ := isOpen_pi_iff.mp hW (e x) hxW
    refine ⟨S, u, (isOpen_set_pi S.finite_toSet (fun i hi => (hu i hi).1)).preimage
      he.continuous, fun i hi => (hu i hi).2, ?_⟩
    intro y hy
    have : y ∈ e ⁻¹' W := hsub hy
    rwa [heW] at this
  choose S u ho hxU hfU using hloc
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun x : tsupport f => e ⁻¹' (S x : Set ν).pi (u x)) ho (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  refine ⟨t.biUnion S, ?_⟩
  have hnonzero (x y : Y) (hx : f x ≠ 0)
      (hxy : ∀ v ∈ t.biUnion S, e x v = e y v) : f x = f y := by
    obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (ht (subset_tsupport f hx))
    have hya : e y ∈ (S a : Set ν).pi (u a) := by
      intro v hv
      rw [← hxy v (Finset.mem_biUnion.mpr ⟨a, hat, hv⟩)]
      exact hxa v hv
    exact (hfU a x hxa).trans (hfU a y hya).symm
  intro x y hxy
  by_cases hx : f x = 0
  · by_cases hy : f y = 0
    · exact hx.trans hy.symm
    · exact (hnonzero y x hy (fun v hv => (hxy v hv).symm)).symm
  · exact hnonzero x y hx hxy

section Restricted

variable {ν : Type*} [DecidableEq ν] (V : ν → Type*)
  [∀ v, TopologicalSpace (V v)] (K : (v : ν) → Set (V v))

abbrev RP := RestrictedProduct V K Filter.cofinite

def integralOutside (S : Finset ν) : Set (RP V K) :=
  {x | ∀ v, v ∉ S → x v ∈ K v}

omit [DecidableEq ν] [∀ v, TopologicalSpace (V v)] in
lemma integralOutside_mono {S T : Finset ν} (hST : S ⊆ T) :
    integralOutside V K S ⊆ integralOutside V K T := by
  intro x hx v hv
  exact hx v (fun hs => hv (hST hs))

omit [DecidableEq ν] in
lemma integralOutside_open (hK : ∀ v, IsOpen (K v)) (S : Finset ν) :
    IsOpen (integralOutside V K S) :=
  RestrictedProduct.isOpen_forall_imp_mem hK

omit [DecidableEq ν] in
lemma integralOutside_closed (hK : ∀ v, IsClosed (K v)) (S : Finset ν) :
    IsClosed (integralOutside V K S) := by
  have he : integralOutside V K S =
      ⋂ v, ⋂ (_ : v ∉ S), (fun x : RP V K => x v) ⁻¹' K v := by
    ext x
    simp [integralOutside]
  rw [he]
  exact isClosed_iInter (fun v => isClosed_iInter (fun _ =>
    (hK v).preimage (RestrictedProduct.continuous_eval v)))

omit [DecidableEq ν] [∀ v, TopologicalSpace (V v)] in
lemma exists_integralOutside (x : RP V K) :
    ∃ S : Finset ν, x ∈ integralOutside V K S := by
  let h := Filter.eventually_cofinite.mp x.2
  refine ⟨h.toFinset, ?_⟩
  intro v hv
  by_contra hnot
  exact hv (h.mem_toFinset.mpr hnot)

lemma compact_subset_integralOutside
    (hK : ∀ v, IsOpen (K v)) {C : Set (RP V K)} (hC : IsCompact C) :
    ∃ S : Finset ν, C ⊆ integralOutside V K S := by
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (integralOutside V K)
    (integralOutside_open V K hK) (by
      intro x _
      obtain ⟨S, hS⟩ := exists_integralOutside V K x
      exact Set.mem_iUnion.mpr ⟨S, hS⟩)
  refine ⟨t.biUnion id, ?_⟩
  intro x hx
  obtain ⟨S, hSt, hxS⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact integralOutside_mono V K (fun v hv => Finset.mem_biUnion.mpr ⟨S, hSt, hv⟩) hxS

omit [DecidableEq ν] in
lemma cofinite_le_principal_compl (S : Finset ν) :
    Filter.cofinite ≤ Filter.principal (S : Set ν)ᶜ := by
  apply Filter.le_principal_iff.mpr
  apply Filter.mem_cofinite.mpr
  simp

/-- Finite coordinates determine the function on a sufficiently large
standard open part of the restricted product; it vanishes outside that part. -/
lemma restricted_finite_control
    [∀ v, T2Space (V v)]
    (hKo : ∀ v, IsOpen (K v)) (hKc : ∀ v, IsClosed (K v))
    (p : ν) (φ : SchwartzBruhat (RP V K)) :
    ∃ S : Finset ν, p ∈ S ∧
      (∀ x, φ.1 x ≠ 0 → x ∈ integralOutside V K S) ∧
      ∀ x y : RP V K,
        x ∈ integralOutside V K S → y ∈ integralOutside V K S →
        (∀ v ∈ S, x v = y v) → φ.1 x = φ.1 y := by
  obtain ⟨S₀, hS₀⟩ := compact_subset_integralOutside V K hKo φ.2.2
  let hle := cofinite_le_principal_compl S₀
  let Y := RestrictedProduct V K (Filter.principal (S₀ : Set ν)ᶜ)
  let inc : Y → RP V K := RestrictedProduct.inclusion V K hle
  have hinc : IsClosedEmbedding inc := by
    refine ⟨RestrictedProduct.isEmbedding_inclusion_principal hle, ?_⟩
    change IsClosed (Set.range (RestrictedProduct.inclusion V K hle))
    rw [RestrictedProduct.range_inclusion]
    exact integralOutside_closed V K hKc S₀
  obtain ⟨T, hT⟩ := finite_coordinates_control
    (fun y : Y => (fun v => y v)) RestrictedProduct.isEmbedding_coe_of_principal
    (φ.1 ∘ inc) (φ.2.1.comp_continuous hinc.continuous)
    (φ.2.2.comp_isClosedEmbedding hinc)
  let S := insert p (S₀ ∪ T)
  have h₀ : S₀ ⊆ S := fun v hv => Finset.mem_insert_of_mem (Finset.mem_union_left T hv)
  have h₁ : T ⊆ S := fun v hv => Finset.mem_insert_of_mem (Finset.mem_union_right S₀ hv)
  refine ⟨S, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro x hx
    exact integralOutside_mono V K h₀ (hS₀ (subset_tsupport φ.1 hx))
  have htransport (x y : RP V K) (hy : y ∈ integralOutside V K S)
      (hxy : ∀ v ∈ S, x v = y v) (hx₀ : x ∈ integralOutside V K S₀) :
      y ∈ integralOutside V K S₀ := by
    intro v hv
    by_cases hvS : v ∈ S
    · rw [← hxy v hvS]
      exact hx₀ v hv
    · exact hy v hvS
  have hnonzero (x y : RP V K) (hfx : φ.1 x ≠ 0)
      (hy : y ∈ integralOutside V K S) (hxy : ∀ v ∈ S, x v = y v) :
      φ.1 x = φ.1 y := by
    have hx₀ := hS₀ (subset_tsupport φ.1 hfx)
    have hy₀ := htransport x y hy hxy hx₀
    let x₀ : Y := ⟨fun v => x v, hx₀⟩
    let y₀ : Y := ⟨fun v => y v, hy₀⟩
    exact hT x₀ y₀ (fun v hv => hxy v (h₁ hv))
  intro x y hx hy hxy
  by_cases hfx : φ.1 x = 0
  · by_cases hfy : φ.1 y = 0
    · exact hfx.trans hfy.symm
    · exact (hnonzero y x hfy hx (fun v hv => (hxy v hv).symm)).symm
  · exact hnonzero x y hfx hy hxy

/-- Extend finitely many coordinates by fixed standard-lattice points. -/
def fill (S : Finset ν) (b : (v : ν) → K v)
    (z : (v : S) → V v.1) : RP V K :=
  ⟨fun v => if hv : v ∈ S then z ⟨v, hv⟩ else (b v).1, by
    apply Filter.Eventually.filter_mono (cofinite_le_principal_compl S)
    intro v hv
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hv
    change (if hv : v ∈ S then z ⟨v, hv⟩ else (b v).1) ∈ K v
    rw [dite_eq_right hv]
    exact (b v).2⟩

omit [∀ v, TopologicalSpace (V v)] in
@[simp] lemma fill_apply_mem (S : Finset ν) (b : (v : ν) → K v)
    (z : (v : S) → V v.1) (v : ν) (hv : v ∈ S) :
    fill V K S b z v = z ⟨v, hv⟩ := by
  simp [fill, hv]

omit [∀ v, TopologicalSpace (V v)] in
@[simp] lemma fill_apply_not_mem (S : Finset ν) (b : (v : ν) → K v)
    (z : (v : S) → V v.1) (v : ν) (hv : v ∉ S) :
    fill V K S b z v = (b v).1 := by
  simp [fill, hv]

omit [∀ v, TopologicalSpace (V v)] in
lemma fill_integralOutside (S : Finset ν) (b : (v : ν) → K v)
    (z : (v : S) → V v.1) : fill V K S b z ∈ integralOutside V K S := by
  intro v hv
  rw [fill_apply_not_mem V K S b z v hv]
  exact (b v).2

lemma continuous_fill (S : Finset ν) (b : (v : ν) → K v) :
    Continuous (fill V K S b) := by
  let Y := RestrictedProduct V K (Filter.principal (S : Set ν)ᶜ)
  let lift : ((v : S) → V v.1) → Y := fun z =>
    ⟨fun v => fill V K S b z v, fill_integralOutside V K S b z⟩
  have hlift : Continuous lift := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    change Continuous (fun z : ((v : S) → V v.1) => fill V K S b z v)
    by_cases hv : v ∈ S
    · have heq : (fun z : ((v : S) → V v.1) => fill V K S b z v) =
          (fun z => z ⟨v, hv⟩) := funext (fun z => fill_apply_mem V K S b z v hv)
      rw [heq]
      exact continuous_apply (⟨v, hv⟩ : S)
    · have heq : (fun z : ((v : S) → V v.1) => fill V K S b z v) =
          (fun _ => (b v).1) := funext (fun z => fill_apply_not_mem V K S b z v hv)
      rw [heq]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion (cofinite_le_principal_compl S)).comp hlift

end Restricted

/-- The local-factorization statement, with the hypotheses of the specification. -/
theorem finite_local_factorization
    {ν : Type*} [DecidableEq ν]
    (V : ν → Type*)
    [∀ v, TopologicalSpace (V v)]
    [∀ v, T2Space (V v)]
    [∀ v, LocallyCompactSpace (V v)]
    [∀ v, TotallyDisconnectedSpace (V v)]
    (K : (v : ν) → Set (V v))
    (hK_compact : ∀ v, IsCompact (K v))
    (hK_open : ∀ v, IsOpen (K v))
    (hK_nonempty : ∀ v, (K v).Nonempty)
    (p : ν)
    (φ : SchwartzBruhat (RestrictedProduct V K Filter.cofinite)) :
    ∃ (S : Finset ν) (n : ℕ) (c : Fin n → ℂ)
      (ψ : Fin n → (v : S) → SchwartzBruhat (V v.1)),
      p ∈ S ∧
      ∀ x : RestrictedProduct V K Filter.cofinite,
        φ.1 x =
          if ∀ v, v ∉ S → x v ∈ K v then
            ∑ j : Fin n,
              c j * ∏ v : S, (ψ j v).1 (x v.1)
          else 0 := by
  obtain ⟨S, hpS, hsupp, hcontrol⟩ := restricted_finite_control V K hK_open
    (fun v => (hK_compact v).isClosed) p φ
  let b : (v : ν) → K v := fun v => ⟨(hK_nonempty v).choose, (hK_nonempty v).choose_spec⟩
  let proj : RP V K → (v : S) → V v.1 := fun x v => x v.1
  have hproj : Continuous proj := continuous_pi (fun v => RestrictedProduct.continuous_eval v.1)
  have hsection (z : (v : S) → V v.1) : proj (fill V K S b z) = z := by
    funext v
    exact fill_apply_mem V K S b z v.1 v.2
  let g : ((v : S) → V v.1) → ℂ := φ.1 ∘ fill V K S b
  have hg_lc : IsLocallyConstant g := φ.2.1.comp_continuous (continuous_fill V K S b)
  have hg_cs : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact (φ.2.2.image hproj)
    intro z hz
    exact ⟨fill V K S b z, subset_tsupport φ.1 hz, hsection z⟩
  obtain ⟨n, c, ψ, hdec⟩ := finite_product_decomposition (fun v : S => V v.1)
    ⟨g, hg_lc, hg_cs⟩
  refine ⟨S, n, c, ψ, hpS, ?_⟩
  intro x
  by_cases hx : ∀ v, v ∉ S → x v ∈ K v
  · rw [ite_eq_left hx]
    calc
      φ.1 x = g (proj x) := hcontrol x (fill V K S b (proj x)) hx
        (fill_integralOutside V K S b (proj x))
        (fun v hv => (fill_apply_mem V K S b (proj x) v hv).symm)
      _ = ∑ j : Fin n, c j * ∏ v : S, (ψ j v).1 (x v.1) := hdec (proj x)
  · rw [ite_eq_right hx]
    by_contra hne
    exact hx (hsupp x hne)

end

end OAI.Analysis.Schwartz.TensorDecomposition.Constructions
