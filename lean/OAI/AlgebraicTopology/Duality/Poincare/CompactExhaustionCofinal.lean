import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Compacts

/-! # Compact Exhaustion Cofinal -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactExhaustionCofinal

/-!
# Compact exhaustions are cofinal among compact supports

The members of mathlib's `CompactExhaustion` form a functor from the ordered
natural numbers to the compact subsets of the underlying space. Every compact
subset lies in one member, so this functor is final. No extra containment or
cofinality hypothesis is imposed on an actual compact exhaustion.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A member of an actual compact exhaustion, bundled as a compact support. -/
def compactExhaustionSupport (K : CompactExhaustion X) (n : ℕ) : Compacts X :=
  ⟨K n, K.isCompact n⟩

@[simp]
theorem coe_compactExhaustionSupport (K : CompactExhaustion X) (n : ℕ) :
    (compactExhaustionSupport K n : Set X) = K n := rfl

/-- The compact supports increase with the index. -/
theorem compactExhaustionSupport_mono (K : CompactExhaustion X) :
    Monotone (compactExhaustionSupport K) :=
  fun _ _ h => K.subset h

/-- Every compact set lies in a member of an actual compact exhaustion. -/
theorem exists_le_compactExhaustionSupport (K : CompactExhaustion X) (L : Compacts X) :
    ∃ n, L ≤ compactExhaustionSupport K n :=
  K.exists_superset_of_isCompact L.isCompact

/-- The genuine inclusions of compact supports in an exhaustion. -/
def compactExhaustionFunctor (K : CompactExhaustion X) : ℕ ⥤ Compacts X :=
  (compactExhaustionSupport_mono K).functor

@[simp]
theorem compactExhaustionFunctor_obj (K : CompactExhaustion X) (n : ℕ) :
    (compactExhaustionFunctor K).obj n = compactExhaustionSupport K n := rfl

@[simp]
theorem compactExhaustionFunctor_map (K : CompactExhaustion X) {m n : ℕ} (h : m ≤ n) :
    (compactExhaustionFunctor K).map (homOfLE h) =
      homOfLE (compactExhaustionSupport_mono K h) := rfl

/-- An actual compact exhaustion is categorically cofinal among all compact supports. -/
instance compactExhaustionFunctor_final (K : CompactExhaustion X) :
    (compactExhaustionFunctor K).Final :=
  (Monotone.final_functor_iff (compactExhaustionSupport_mono K)).mpr
    (exists_le_compactExhaustionSupport K)

end OAI.AlgebraicTopology.Duality.Poincare.CompactExhaustionCofinal
