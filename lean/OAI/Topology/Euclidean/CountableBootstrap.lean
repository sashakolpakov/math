import OAI.Topology.Euclidean.BoxExhaustion

/-! # Countable Bootstrap -/

namespace OAI.Topology.Euclidean.CountableBootstrap.Globalization

/-!
# Gluing a property from a countable basis

The hypotheses record exactly the two global steps needed after a local
comparison theorem: gluing over two open sets, with their intersection, and
passage to an increasing countable union. Neither step is inferred from the
local assertion. The final specialization uses actual rational open boxes.
-/

open Set _root_.TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- Finite unions of members of an intersection-closed family satisfy any
property with the stated two-open-set gluing rule. -/
theorem property_finite_union
    (P : Set X → Prop) (C : Set (Set X))
    (hopen : ∀ U ∈ C, IsOpen U)
    (hempty : P ∅) (hbase : ∀ U ∈ C, P U)
    (hinter : ∀ U ∈ C, ∀ V ∈ C, U ∩ V ∈ C)
    (hglue : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    {ι : Type*} (s : Finset ι) (b : ι → Set X)
    (hb : ∀ i ∈ s, b i ∈ C) : P (⋃ i ∈ s, b i) := by
  classical
  have hall : ∀ t : Finset ι, (∀ i ∈ t, b i ∈ C) →
      P (⋃ i ∈ t, b i) ∧ ∀ U ∈ C, P (U ∩ ⋃ i ∈ t, b i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        constructor
        · simpa using hempty
        · intro U _
          simpa using hempty
    | @insert i t hit ih =>
        intro ht
        have hiC := ht i (Finset.mem_insert_self i t)
        have htC : ∀ j ∈ t, b j ∈ C := fun j hj => ht j (Finset.mem_insert_of_mem hj)
        obtain ⟨hPt, hPinter⟩ := ih htC
        have hot : IsOpen (⋃ j ∈ t, b j) :=
          isOpen_biUnion fun j hj => hopen (b j) (htC j hj)
        have hPi := hbase (b i) hiC
        have hoi := hopen (b i) hiC
        simp only [Finset.set_biUnion_insert]
        refine ⟨hglue _ _ hoi hot hPi hPt (hPinter (b i) hiC), ?_⟩
        intro U hU
        rw [inter_union_distrib_left]
        have hUiC := hinter U hU (b i) hiC
        apply hglue _ _ ((hopen U hU).inter hoi) ((hopen U hU).inter hot)
          (hbase _ hUiC) (hPinter U hU)
        have heq : (U ∩ b i) ∩ (U ∩ ⋃ j ∈ t, b j) =
            (U ∩ b i) ∩ ⋃ j ∈ t, b j := by
          ext x
          simp only [mem_inter_iff]
          tauto
        rw [heq]
        exact hPinter _ hUiC
  exact (hall s hb).1

/-- A finite cover need not be a good cover: it is enough to know the property
on each of its nonempty finite intersections. -/
theorem property_finite_union_of_intersections
    (P : Set X → Prop) (hempty : P ∅)
    (hglue : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    {ι : Type*} (s : Finset ι) (b : ι → Set X)
    (hopen : ∀ i ∈ s, IsOpen (b i))
    (hintersections : ∀ t : Finset ι, t ⊆ s → t.Nonempty → P (⋂ i ∈ t, b i)) :
    P (⋃ i ∈ s, b i) := by
  classical
  let C : Set (Set X) := {U | ∃ t : Finset ι,
    t ⊆ s ∧ t.Nonempty ∧ U = ⋂ i ∈ t, b i}
  have hCo : ∀ U ∈ C, IsOpen U := by
    rintro U ⟨t, ht, _, rfl⟩
    exact isOpen_biInter_finset fun i hi => hopen i (ht hi)
  have hCP : ∀ U ∈ C, P U := by
    rintro U ⟨t, ht, hne, rfl⟩
    exact hintersections t ht hne
  have hCi : ∀ U ∈ C, ∀ V ∈ C, U ∩ V ∈ C := by
    rintro U ⟨t, ht, hne, rfl⟩ V ⟨u, hu, _, rfl⟩
    refine ⟨t ∪ u, Finset.union_subset ht hu, hne.mono Finset.subset_union_left, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_iInter, Finset.mem_union]
    aesop
  apply property_finite_union P C hCo hempty hCP hCi hglue s b
  intro i hi
  refine ⟨{i}, Finset.singleton_subset_iff.mpr hi, Finset.singleton_nonempty i, ?_⟩
  simp

/-- The finite-cover form of the preceding criterion. -/
theorem property_of_finite_cover
    (P : Set X → Prop) (hempty : P ∅)
    (hglue : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    {ι : Type*} (s : Finset ι) (b : ι → Set X)
    (hopen : ∀ i ∈ s, IsOpen (b i))
    (hintersections : ∀ t : Finset ι, t ⊆ s → t.Nonempty → P (⋂ i ∈ t, b i))
    (hcover : (⋃ i ∈ s, b i) = univ) : P univ := by
  rw [← hcover]
  exact property_finite_union_of_intersections P hempty hglue s b hopen hintersections

/-- A countable family whose pairwise intersections remain in the family or
are empty supports a local-to-global argument, provided both gluing hypotheses
have actually been proved for the property in question. -/
theorem property_of_countable_cover
    {ι : Type*} [Countable ι] (b : ι → Set X)
    (hopen : ∀ i, IsOpen (b i))
    (hinter : ∀ i j, (∃ k, b i ∩ b j = b k) ∨ b i ∩ b j = ∅)
    (P : Set X → Prop) (hempty : P ∅) (hbase : ∀ i, P (b i))
    (hglue : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    (hlimit : ∀ a : ℕ → Set X, Monotone a → (∀ n, IsOpen (a n)) →
      (∀ n, P (a n)) → P (⋃ n, a n))
    (U : Set X) (hcover : ∀ x ∈ U, ∃ i, x ∈ b i ∧ b i ⊆ U) : P U := by
  let C : Set (Set X) := {V | V = ∅ ∨ ∃ i, V = b i}
  have hCo : ∀ V ∈ C, IsOpen V := by
    rintro V (rfl | ⟨i, rfl⟩)
    · exact isOpen_empty
    · exact hopen i
  have hCP : ∀ V ∈ C, P V := by
    rintro V (rfl | ⟨i, rfl⟩)
    · exact hempty
    · exact hbase i
  have hCi : ∀ V ∈ C, ∀ W ∈ C, V ∩ W ∈ C := by
    rintro V (rfl | ⟨i, rfl⟩) W hW
    · exact Or.inl (empty_inter W)
    · rcases hW with rfl | ⟨j, rfl⟩
      · exact Or.inl (inter_empty (b i))
      · rcases hinter i j with ⟨k, hk⟩ | he
        · exact Or.inr ⟨k, hk⟩
        · exact Or.inl he
  have hstage : ∀ n, P (BoxExhaustion.Globalization.CountableFamily.stage b U n) := by
    intro n
    exact property_finite_union P C hCo hempty hCP hCi hglue
      (BoxExhaustion.Globalization.CountableFamily.indices b U n) b (fun i _ => Or.inr ⟨i, rfl⟩)
  rw [← BoxExhaustion.Globalization.CountableFamily.iUnion_stage b U hcover]
  exact hlimit (BoxExhaustion.Globalization.CountableFamily.stage b U) (BoxExhaustion.Globalization.CountableFamily.stage_mono b U)
    (BoxExhaustion.Globalization.CountableFamily.isOpen_stage b U hopen) hstage

/-- The preceding criterion applies to every open set when the countable
family is a topological basis. -/
theorem property_of_countable_basis
    {ι : Type*} [Countable ι] (b : ι → Set X)
    (hbasis : IsTopologicalBasis (range b))
    (hinter : ∀ i j, (∃ k, b i ∩ b j = b k) ∨ b i ∩ b j = ∅)
    (P : Set X → Prop) (hempty : P ∅) (hbase : ∀ i, P (b i))
    (hglue : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    (hlimit : ∀ a : ℕ → Set X, Monotone a → (∀ n, IsOpen (a n)) →
      (∀ n, P (a n)) → P (⋃ n, a n))
    (U : Set X) (hU : IsOpen U) : P U := by
  apply property_of_countable_cover b
    (fun i => hbasis.isOpen (mem_range_self i)) hinter P hempty hbase hglue hlimit U
  intro x hx
  obtain ⟨V, ⟨i, rfl⟩, hxi, hiU⟩ := hbasis.exists_subset_of_mem_open hx hU
  exact ⟨i, hxi, hiU⟩

/-- Concrete specialization to the usual rational boxes in a finite real
coordinate space. The basis and intersection conditions are discharged. -/
theorem property_of_rational_boxes
    {ι : Type*} [Finite ι] (P : Set (ι → ℝ) → Prop)
    (hempty : P ∅) (hbox : ∀ B : BoxBasis.Globalization.RationalBox ι, P B.carrier)
    (hglue : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    (hlimit : ∀ a : ℕ → Set (ι → ℝ), Monotone a → (∀ n, IsOpen (a n)) →
      (∀ n, P (a n)) → P (⋃ n, a n))
    (U : Set (ι → ℝ)) (hU : IsOpen U) : P U :=
  property_of_countable_basis BoxBasis.Globalization.RationalBox.carrier
    BoxBasis.Globalization.RationalBox.isTopologicalBasis_carrier BoxBasis.Globalization.RationalBox.inter_eq_carrier_or_empty
    P hempty hbox hglue hlimit U hU

end OAI.Topology.Euclidean.CountableBootstrap.Globalization
