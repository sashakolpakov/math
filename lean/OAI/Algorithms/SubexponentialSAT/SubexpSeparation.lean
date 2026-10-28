import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Moments
import OAI.Algorithms.SubexponentialSAT.SubexpDirectSums
import OAI.Algorithms.SubexponentialSAT.SubexpCosetCount

namespace OAI.Algorithms

/-!
# Arbitrarily many independent symbolic color groups

Section 4.3 of `source/subexponential-sat.txt`.  The color type is an arbitrary
finite type, so the results apply to `Fin r` with no fixed bound on `r`.
Every sum and product is a genuine finite operation in a commutative semiring.
The independence assumptions are pointwise statements about group values,
not assumptions about the desired sum identity.
-/

namespace SubexponentialSAT.SubexpSeparation

open scoped BigOperators

section IndependentProducts

variable {R G : Type*} {X : G → Type*} [CommSemiring R]
  [Fintype G] [DecidableEq G] [∀ g, Fintype (X g)]

/-- Finite distributivity over all independent color choices. -/
theorem sum_prod_eq_prod_sum (f : ∀ g, X g → R) :
    (∑ x : ∀ g, X g, ∏ g, f g (x g)) = ∏ g, ∑ y : X g, f g y :=
  (Fintype.prod_sum f).symm

/-- Equation (4.6) for fixed outer data.  The group of color `g` depends only
on the `g` input.  All other inputs may therefore be replaced by their fixed
representatives when evaluating that group, while the actual weight stays. -/
theorem weighted_separation (reps : ∀ g, X g)
    (A : G → (∀ g, X g) → R) (w : (∀ g, X g) → R)
    (c : R) (wg : ∀ g, X g → R)
    (hA : ∀ g x y, x g = y g → A g x = A g y)
    (hw : ∀ x, w x = c * ∏ g, wg g (x g)) :
    (∑ x : ∀ g, X g, w x * ∏ g, A g x) =
      c * ∏ g, ∑ y : X g, wg g y * A g (Function.update reps g y) := by
  calc
    _ = ∑ x : ∀ g, X g,
        c * ∏ g, wg g (x g) * A g (Function.update reps g (x g)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hw, mul_assoc, ← Finset.prod_mul_distrib]
      apply congrArg (c * ·)
      apply Finset.prod_congr rfl
      intro g hg
      rw [hA g x (Function.update reps g (x g)) (by simp)]
    _ = c * (∑ x : ∀ g, X g,
        ∏ g, wg g (x g) * A g (Function.update reps g (x g))) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (c * ·)
      (sum_prod_eq_prod_sum (fun g y => wg g y * A g (Function.update reps g y)))

end IndependentProducts

section OuterData

variable {R Ω O G : Type*} {X : O → G → Type*} [CommSemiring R]
  [Fintype Ω] [Fintype O] [Fintype G] [DecidableEq G]
  [∀ o g, Fintype (X o g)]

/-- An actual equivalence reindexes the full assignment space by its outer
data and one independent inner choice for each color. -/
theorem sum_reindex_fibers (e : Ω ≃ Σ o, ∀ g, X o g) (f : Ω → R) :
    (∑ z, f z) = ∑ o, ∑ x : ∀ g, X o g, f (e.symm ⟨o, x⟩) := by
  calc
    _ = ∑ z : Σ o, ∀ g, X o g, f (e.symm z) :=
      Fintype.sum_equiv e _ _ (fun z => by rw [e.symm_apply_apply])
    _ = _ := Fintype.sum_sigma _

/-- Full-input form of (4.6), including a proved bijective reindexing and an
arbitrary finite number of color groups. -/
theorem weighted_separation_equiv (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (A : G → Ω → R) (w : Ω → R)
    (c : O → R) (wg : ∀ o g, X o g → R)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ o x, w (e.symm ⟨o, x⟩) = c o * ∏ g, wg o g (x g)) :
    (∑ z, w z * ∏ g, A g z) =
      ∑ o, c o * ∏ g, ∑ y : X o g,
        wg o g y * A g (e.symm ⟨o, Function.update (reps o) g y⟩) := by
  rw [sum_reindex_fibers e]
  apply Finset.sum_congr rfl
  intro o ho
  exact weighted_separation (reps o) (fun g x => A g (e.symm ⟨o, x⟩))
    (fun x => w (e.symm ⟨o, x⟩)) (c o) (wg o) (hA o) (hw o)

/-- Scalar weights may be embedded into the symbolic value ring.  For
polynomial values, instantiate `φ` with the appropriate constant homomorphism. -/
theorem weighted_separation_equiv_map_weights {S : Type*} [CommSemiring S]
    (φ : S →+* R) (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (A : G → Ω → R) (w : Ω → S)
    (c : O → S) (wg : ∀ o g, X o g → S)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ o x, w (e.symm ⟨o, x⟩) = c o * ∏ g, wg o g (x g)) :
    (∑ z, φ (w z) * ∏ g, A g z) =
      ∑ o, φ (c o) * ∏ g, ∑ y : X o g,
        φ (wg o g y) * A g (e.symm ⟨o, Function.update (reps o) g y⟩) := by
  apply weighted_separation_equiv e reps A (fun z => φ (w z))
    (fun o => φ (c o)) (fun o g y => φ (wg o g y)) hA
  intro o x
  rw [hw, map_mul, map_prod]

end OuterData

section CoordinateProducts

variable {R G I : Type*} [CommMonoid R] [Fintype G] [Fintype I] [DecidableEq I]

/-- A product over coordinates splits across any pairwise-disjoint finite
family of supports, together with the complement of their union. -/
theorem coordinate_prod_partition (S : G → Finset I)
    (hS : Pairwise (fun g h => Disjoint (S g) (S h))) (f : I → R) :
    (∏ i, f i) =
      (∏ i : ↥((Finset.univ.biUnion S)ᶜ), f i.val) *
        ∏ g, ∏ i : S g, f i.val := by
  have hinner : (∏ g, ∏ i : S g, f i.val) = ∏ g, ∏ i ∈ S g, f i := by
    apply Finset.prod_congr rfl
    intro g hg
    exact Finset.prod_coe_sort (S g) f
  rw [Finset.prod_coe_sort ((Finset.univ.biUnion S)ᶜ) f, hinner,
    ← Finset.prod_compl_mul_prod (Finset.univ.biUnion S) f,
    Finset.prod_biUnion (fun g _ h _ hgh => hS hgh)]

end CoordinateProducts

section MomentWeights

variable {R G I V : Type*} [CommSemiring R]
  [Fintype G] [Fintype I] [DecidableEq I]

/-- The finite-support monomial weight from the actual moment definition
splits into one weight per color and a complementary-coordinate weight. -/
theorem momentWeight_partition (S : G → Finset I)
    (hS : Pairwise (fun g h => Disjoint (S g) (S h)))
    (a : I →₀ ℕ) (v : I → R) :
    Moments.weight a v =
      (∏ i : ↥((Finset.univ.biUnion S)ᶜ), v i.val ^ a i.val) *
        ∏ g, ∏ i : S g, v i.val ^ a i.val := by
  rw [Moments.weight_eq_prod_univ]
  exact coordinate_prod_partition S hS (fun i => v i ^ a i)

/-- Restriction equalities, such as those proved for actual coordinate
reconstruction, give exact factorization for any coordinate-label function.
No additive or multiplicative property of `lift` is assumed. -/
theorem momentWeight_of_components (S : G → Finset I)
    (hS : Pairwise (fun g h => Disjoint (S g) (S h)))
    (a : I →₀ ℕ) (lift : V → R) (v : I → V)
    (vstar : ↥((Finset.univ.biUnion S)ᶜ) → V) (vg : ∀ g, S g → V)
    (hstar : (fun i : ↥((Finset.univ.biUnion S)ᶜ) => v i.val) = vstar)
    (hg : ∀ g, (fun i : S g => v i.val) = vg g) :
    Moments.weight a (fun i => lift (v i)) =
      (∏ i : ↥((Finset.univ.biUnion S)ᶜ), lift (vstar i) ^ a i.val) *
        ∏ g, ∏ i : S g, lift (vg g i) ^ a i.val := by
  rw [momentWeight_partition S hS]
  apply congrArg₂ (· * ·)
  · exact congrArg
      (fun f : ↥((Finset.univ.biUnion S)ᶜ) → V =>
        ∏ i : ↥((Finset.univ.biUnion S)ᶜ), lift (f i) ^ a i.val) hstar
  · apply Finset.prod_congr rfl
    intro g hgin
    exact congrArg (fun f : S g → V => ∏ i : S g, lift (f i) ^ a i.val) (hg g)

end MomentWeights

section ActualCoordinateWeights

variable {R K G I : Type*} [CommSemiring R] [Field K]
  [Fintype G] [Fintype I] [DecidableEq I]

/-- Exact moment weights for the actual zero-extension-and-sum coordinate
assembly. Pairwise disjointness alone supplies all required restrictions. -/
theorem momentWeight_coordinateAssemble (S : G → Finset I)
    (hS : Pairwise (fun g h => Disjoint (S g) (S h)))
    (a : I →₀ ℕ) (lift : K → R)
    (pieces : (↥((Finset.univ.biUnion S)ᶜ) → K) × (∀ g, S g → K)) :
    Moments.weight a (fun i => lift (SubexpDirectSums.coordinateAssemble S pieces i)) =
      (∏ i : ↥((Finset.univ.biUnion S)ᶜ), lift (pieces.1 i) ^ a i.val) *
        ∏ g, ∏ i : S g, lift (pieces.2 g i) ^ a i.val := by
  apply momentWeight_of_components S hS a lift _ pieces.1 pieces.2
  · funext i
    exact SubexpDirectSums.coordinateAssemble_outside S pieces i.val i.property
  · intro g
    funext i
    exact SubexpDirectSums.coordinateAssemble_on_color S hS pieces g i.val i.property

/-- The same identity stated for the inverse of the actual coordinate linear
equivalence, ready to compose with the family quotient/coset equivalence. -/
theorem momentWeight_coordinateSplit_symm (S : G → Finset I)
    (hS : Pairwise (fun g h => Disjoint (S g) (S h)))
    (a : I →₀ ℕ) (lift : K → R)
    (pieces : (↥((Finset.univ.biUnion S)ᶜ) → K) × (∀ g, S g → K)) :
    Moments.weight a
        (fun i => lift ((SubexpDirectSums.coordinateSplitEquiv S hS).symm pieces i)) =
      (∏ i : ↥((Finset.univ.biUnion S)ᶜ), lift (pieces.1 i) ^ a i.val) *
        ∏ g, ∏ i : S g, lift (pieces.2 g i) ^ a i.val :=
  momentWeight_coordinateAssemble S hS a lift pieces

end ActualCoordinateWeights

section ActualCosetWeights

variable {r : ℕ} {R K I : Type*} [CommSemiring R] [Field K]
  [Fintype K] [Fintype I] [DecidableEq I]

omit [Fintype K] in
/-- The exact weight identity for the layout's actual multicolor coordinate
and quotient reconstruction. It discharges the scalar factorization premise
of `weighted_separation_equiv` with no additional weight assumption. -/
theorem momentWeight_coordinateReconstruct (S : Fin r → Finset I)
    (hS : Pairwise (fun g h => Disjoint (S g) (S h)))
    (L : ∀ g, Submodule K (S g → K))
    (o : SubexpCosetCount.CoordinateOuterData S L)
    (x : ∀ g, CosetCardinality.CosetFiber (L g) (o.2 g))
    (a : I →₀ ℕ) (lift : K → R) :
    Moments.weight a
        (fun i => lift (SubexpCosetCount.coordinateReconstruct S hS L o x i)) =
      (∏ i : ↥((Finset.univ.biUnion S)ᶜ), lift (o.1 i) ^ a i.val) *
        ∏ g, ∏ i : S g, lift ((x g).val i) ^ a i.val := by
  rw [SubexpCosetCount.coordinateReconstruct_eq]
  exact momentWeight_coordinateAssemble S hS a lift (o.1, fun g => (x g).val)

end ActualCosetWeights

end SubexponentialSAT.SubexpSeparation

end OAI.Algorithms
