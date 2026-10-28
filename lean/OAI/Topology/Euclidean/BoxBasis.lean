import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Pi
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Box Basis -/

namespace OAI.Topology.Euclidean.BoxBasis.Globalization

noncomputable section

/-!
# A countable basis of rational open boxes

The carrier is the usual product of open real intervals with rational endpoints.
It is also identified directly with `BoxIntegral.Box.Ioo`. For a finite coordinate
type these carriers form a countable topological basis. Intersections are convex,
and the intersection of two basis boxes is another basis box or is empty.
-/

open Set _root_.TopologicalSpace

/-- Strict rational lower and upper endpoints in every coordinate. -/
def RationalBox (ι : Type*) :=
  { endpoints : (ι → ℚ) × (ι → ℚ) // ∀ i, endpoints.1 i < endpoints.2 i }

namespace RationalBox

variable {ι : Type*}

instance [Finite ι] : Countable (RationalBox ι) :=
  inferInstanceAs (Countable { endpoints : (ι → ℚ) × (ι → ℚ) //
    ∀ i, endpoints.1 i < endpoints.2 i })

/-- The rational lower corner. -/
def lower (B : RationalBox ι) : ι → ℚ := B.val.1

/-- The rational upper corner. -/
def upper (B : RationalBox ι) : ι → ℚ := B.val.2

theorem lower_lt_upper (B : RationalBox ι) (i : ι) : B.lower i < B.upper i :=
  B.property i

/-- The corresponding standard mathlib real box. -/
def toBox (B : RationalBox ι) : BoxIntegral.Box ι where
  lower i := B.lower i
  upper i := B.upper i
  lower_lt_upper i := Rat.cast_lt.mpr (B.lower_lt_upper i)

/-- The open carrier of a rational box in the ordinary real product topology. -/
def carrier (B : RationalBox ι) : Set (ι → ℝ) :=
  univ.pi fun i => Ioo (B.lower i : ℝ) (B.upper i : ℝ)

theorem carrier_eq_box_Ioo (B : RationalBox ι) :
    B.carrier = BoxIntegral.Box.Ioo B.toBox := rfl

@[simp]
theorem mem_carrier (B : RationalBox ι) (x : ι → ℝ) :
    x ∈ B.carrier ↔ ∀ i, (B.lower i : ℝ) < x i ∧ x i < (B.upper i : ℝ) :=
  mem_univ_pi

theorem carrier_nonempty (B : RationalBox ι) : B.carrier.Nonempty := by
  refine ⟨fun i => ((B.lower i : ℝ) + (B.upper i : ℝ)) / 2, ?_⟩
  rw [mem_carrier]
  intro i
  have h : (B.lower i : ℝ) < (B.upper i : ℝ) :=
    Rat.cast_lt.mpr (B.lower_lt_upper i)
  constructor <;> linarith

theorem isOpen_carrier [Finite ι] (B : RationalBox ι) : IsOpen B.carrier :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem convex_carrier (B : RationalBox ι) : Convex ℝ B.carrier :=
  convex_pi fun _ _ => convex_Ioo _ _

/-- Every open neighbourhood contains a rational open box around its point. -/
theorem exists_mem_subset [Finite ι] {U : Set (ι → ℝ)} (hU : IsOpen U)
    {x : ι → ℝ} (hx : x ∈ U) :
    ∃ B : RationalBox ι, x ∈ B.carrier ∧ B.carrier ⊆ U := by
  obtain ⟨u, hu, huU⟩ := isOpen_pi_iff'.mp hU x hx
  have hinterval : ∀ i, ∃ a b : ℚ, a < b ∧
      x i ∈ Ioo (a : ℝ) (b : ℝ) ∧ Ioo (a : ℝ) (b : ℝ) ⊆ u i := by
    intro i
    obtain ⟨v, hv, hxv, hvu⟩ :=
      Real.isTopologicalBasis_Ioo_rat.exists_subset_of_mem_open (hu i).2 (hu i).1
    simp only [mem_iUnion, mem_singleton_iff] at hv
    obtain ⟨a, b, hab, rfl⟩ := hv
    exact ⟨a, b, hab, hxv, hvu⟩
  choose a b hab hxab habu using hinterval
  let B : RationalBox ι := ⟨(a, b), hab⟩
  refine ⟨B, ?_, ?_⟩
  · exact (mem_carrier B x).mpr hxab
  · intro y hy
    apply huU
    intro i _
    exact habu i ((mem_carrier B y).mp hy i)

theorem isTopologicalBasis_carrier [Finite ι] :
    IsTopologicalBasis (range (RationalBox.carrier : RationalBox ι → Set (ι → ℝ))) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨B, rfl⟩
    exact B.isOpen_carrier
  · intro x U hx hU
    obtain ⟨B, hxB, hBU⟩ := exists_mem_subset hU hx
    exact ⟨B.carrier, mem_range_self B, hxB, hBU⟩

theorem countable_range_carrier [Finite ι] :
    (range (RationalBox.carrier : RationalBox ι → Set (ι → ℝ))).Countable :=
  countable_range _

/-- Coordinatewise maximum and minimum give the nonempty intersection box. -/
def inter (B C : RationalBox ι)
    (h : ∀ i, max (B.lower i) (C.lower i) < min (B.upper i) (C.upper i)) :
    RationalBox ι :=
  ⟨(fun i => max (B.lower i) (C.lower i), fun i => min (B.upper i) (C.upper i)), h⟩

@[simp]
theorem lower_inter (B C : RationalBox ι)
    (h : ∀ i, max (B.lower i) (C.lower i) < min (B.upper i) (C.upper i)) (i : ι) :
    (B.inter C h).lower i = max (B.lower i) (C.lower i) := rfl

@[simp]
theorem upper_inter (B C : RationalBox ι)
    (h : ∀ i, max (B.lower i) (C.lower i) < min (B.upper i) (C.upper i)) (i : ι) :
    (B.inter C h).upper i = min (B.upper i) (C.upper i) := rfl

theorem carrier_inter (B C : RationalBox ι)
    (h : ∀ i, max (B.lower i) (C.lower i) < min (B.upper i) (C.upper i)) :
    (B.inter C h).carrier = B.carrier ∩ C.carrier := by
  apply Set.ext
  intro x
  rw [mem_inter_iff, mem_carrier, mem_carrier, mem_carrier]
  simp only [lower_inter, upper_inter, Rat.cast_max, Rat.cast_min, max_lt_iff, lt_min_iff]
  constructor
  · intro hx
    exact ⟨fun i => ⟨(hx i).1.1, (hx i).2.1⟩,
      fun i => ⟨(hx i).1.2, (hx i).2.2⟩⟩
  · rintro ⟨hxB, hxC⟩ i
    exact ⟨⟨(hxB i).1, (hxC i).1⟩, ⟨(hxB i).2, (hxC i).2⟩⟩

theorem inter_eq_carrier_or_empty (B C : RationalBox ι) :
    (∃ D : RationalBox ι, B.carrier ∩ C.carrier = D.carrier) ∨
      B.carrier ∩ C.carrier = ∅ := by
  classical
  by_cases h : ∀ i, max (B.lower i) (C.lower i) < min (B.upper i) (C.upper i)
  · exact Or.inl ⟨B.inter C h, (carrier_inter B C h).symm⟩
  · right
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply h
    intro i
    have hxB := (mem_carrier B x).mp hx.1 i
    have hxC := (mem_carrier C x).mp hx.2 i
    have hreal : max (B.lower i : ℝ) (C.lower i : ℝ) <
        min (B.upper i : ℝ) (C.upper i : ℝ) :=
      (max_lt hxB.1 hxC.1).trans (lt_min hxB.2 hxC.2)
    exact (Rat.cast_lt (K := ℝ)).mp
      (by simpa only [Rat.cast_max, Rat.cast_min] using hreal)

/-- Arbitrary intersections are convex, in particular every finite intersection is convex. -/
theorem convex_iInter {κ : Sort*} (B : κ → RationalBox ι) :
    Convex ℝ (⋂ k, (B k).carrier) :=
  _root_.convex_iInter fun k => (B k).convex_carrier

theorem convex_biInter {κ : Type*} (s : Set κ) (B : κ → RationalBox ι) :
    Convex ℝ (⋂ k ∈ s, (B k).carrier) :=
  convex_iInter₂ fun k _ => (B k).convex_carrier

theorem isOpen_biInter_finset [Finite ι] {κ : Type*} (s : Finset κ)
    (B : κ → RationalBox ι) : IsOpen (⋂ k ∈ s, (B k).carrier) :=
  _root_.isOpen_biInter_finset fun k _ => (B k).isOpen_carrier

end RationalBox

end

end OAI.Topology.Euclidean.BoxBasis.Globalization
