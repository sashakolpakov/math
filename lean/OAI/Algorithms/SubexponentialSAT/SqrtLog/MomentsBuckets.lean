import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBoolean

namespace OAI.Algorithms

/-! Actual attained labels and their Boolean fibers. The label codomain need
not be finite: integer signature vectors are allowed. Enumeration is the
image of each finite head assignment set, followed by its actual fibers. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

section Fibers

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A L : G → Type*} [∀ g, Fintype (A g)] [∀ g, DecidableEq (L g)]

/-- The concrete finite list of attained signatures, represented as a finset. -/
def attainedLabels (label : ∀ g, A g → L g) (g : G) : Finset (L g) :=
  Finset.univ.image (label g)

abbrev LabelValue (label : ∀ g, A g → L g) (g : G) :=
  {y : L g // y ∈ attainedLabels label g}

abbrev LabelBucket (label : ∀ g, A g → L g) (g : G) (y : LabelValue label g) :=
  {a : A g // label g a = y.val}

/-- No rectangularity or equal-fiber-size premise occurs in this equivalence. -/
def actualBucketEquiv (label : ∀ g, A g → L g) :
    (∀ g, A g) ≃ Σ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g) where
  toFun a := ⟨fun g => ⟨label g (a g), Finset.mem_image.mpr ⟨a g, Finset.mem_univ _, rfl⟩⟩,
    fun g => ⟨a g, rfl⟩⟩
  invFun y := fun g => (y.2 g).val
  left_inv a := rfl
  right_inv y := by
    rcases y with ⟨y, a⟩
    have hy : (fun g => (⟨label g (a g).val,
        Finset.mem_image.mpr ⟨(a g).val, Finset.mem_univ _, rfl⟩⟩ : LabelValue label g)) = y := by
      funext g
      apply Subtype.ext
      exact (a g).property
    apply Sigma.ext hy
    apply Function.hfunext rfl
    intro g g' hgg
    cases hgg
    apply Subtype.heq_iff_coe_eq _ |>.mpr
    · rfl
    · intro z
      change (label g z = label g (a g).val) ↔ (label g z = (y g).val)
      rw [(a g).property]

/-- Exact summation over the attained signature tuples and their fibers. -/
theorem sum_actual_buckets {B : Type*} [CommSemiring B]
    (label : ∀ g, A g → L g) (f : (∀ g, A g) → B) :
    (∑ a, f a) = ∑ y : ∀ g, LabelValue label g,
      ∑ a : ∀ g, LabelBucket label g (y g), f (fun g => (a g).val) := by
  classical
  exact SubexpSeparation.sum_reindex_fibers (actualBucketEquiv label) f

omit [Fintype G] [DecidableEq G] in
theorem attainedLabels_card_le (label : ∀ g, A g → L g) (g : G) :
    (attainedLabels label g).card ≤ Fintype.card (A g) := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

end Fibers

section BooleanFibers

variable {V G : Type*} [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G]
variable {L : G → Type*} [∀ g, DecidableEq (L g)]

instance headFintype (head : V → G) (g : G) : Fintype (Head head g) :=
  inferInstanceAs (Fintype {v : V // head v = g})

instance headDecidableEq (head : V → G) (g : G) : DecidableEq (Head head g) :=
  inferInstanceAs (DecidableEq {v : V // head v = g})

def booleanBucketEquiv (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g) :
    (V → Bool) ≃ Σ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g) :=
  (headEquiv head).trans (actualBucketEquiv label)

/-- The actual bucket product has exactly the original Boolean mass. -/
theorem sum_boolean_actual_buckets {B : Type*} [CommSemiring B]
    (head : V → G) (label : ∀ g, (Head head g → Bool) → L g)
    (f : (V → Bool) → B) :
    (∑ x, f x) = ∑ y : ∀ g, LabelValue label g,
      ∑ a : ∀ g, LabelBucket label g (y g), f (assemble head (fun g => (a g).val)) := by
  classical
  exact SubexpSeparation.sum_reindex_fibers (booleanBucketEquiv head label) f

end BooleanFibers

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
