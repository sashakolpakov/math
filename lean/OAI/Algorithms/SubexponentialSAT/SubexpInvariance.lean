import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Counting
import OAI.Algorithms.SubexponentialSAT.SubexpDirectSums

namespace OAI.Algorithms

/-!
# Arbitrarily many colors: exact dependence on one inner coordinate

For a row of color g, every other color subspace is contained in its kernel.
After fixing the outer datum and one coset in each component, this forces the
row residue, its fixed chosen lift, and the actual symbolic factor group to
depend only on the g component. Coordinate lifts need not preserve addition.
-/

namespace SubexponentialSAT.SubexpInvariance

open scoped BigOperators
open CosetInvariance

section Linear

variable {R M E G : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup E] [Module R E] [Fintype G]
  {V : G → Type*} [∀ h, AddCommGroup (V h)] [∀ h, Module R (V h)]

/-- Assemble an ambient input from a fixed outer part and its color blocks. -/
def assemble (base : M) (embed : ∀ h, V h →ₗ[R] M) (x : ∀ h, V h) : M :=
  base + ∑ h, embed h (x h)

/-- Changing just one color block changes the ambient input by exactly
the zero-extended difference of that block. -/
theorem assemble_sub_eq (base : M) (embed : ∀ h, V h →ₗ[R] M)
    (x y : ∀ h, V h) (g : G) (hother : ∀ h, h ≠ g → x h = y h) :
    assemble base embed x - assemble base embed y = embed g (x g - y g) := by
  classical
  simp only [assemble, add_sub_add_left_eq_sub]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single g]
  · exact (map_sub (embed g) (x g) (y g)).symm
  · intro h _ hh
    rw [hother h hh, sub_self]
  · simp

/-- Killing every other color gives equality for arbitrary tuples in fixed
component cosets, provided their own-color components agree. -/
theorem linear_map_assemble_eq (L : M →ₗ[R] E)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G) (hK : ∀ h, h ≠ g → K h ≤ LinearMap.ker (L.comp (embed h)))
    (base : M) {x y : ∀ h, V h} (hown : x g = y g)
    (hcoset : ∀ h, h ≠ g → x h - y h ∈ K h) :
    L (assemble base embed x) = L (assemble base embed y) := by
  classical
  simp only [assemble, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : h = g
  · subst h
    rw [hown]
  · exact linear_map_eq_of_sub_mem (L.comp (embed h)) (K h) (hK h hh)
      (hcoset h hh)

/-- Product-coordinate specialization, using genuine single-coordinate
linear embeddings rather than a functional-dependence assumption. -/
theorem linear_map_pi_eq [DecidableEq G] (L : (∀ h, V h) →ₗ[R] E)
    (K : ∀ h, Submodule R (V h)) (g : G)
    (hK : ∀ h, h ≠ g →
      K h ≤ LinearMap.ker (L.comp (LinearMap.single R V h)))
    {x y : ∀ h, V h} (hown : x g = y g)
    (hcoset : ∀ h, h ≠ g → x h - y h ∈ K h) :
    L x = L y := by
  simpa only [assemble, LinearMap.single_apply, Finset.univ_sum_single, zero_add]
    using linear_map_assemble_eq L K (LinearMap.single R V) g hK 0 hown hcoset

end Linear

section Beta

variable {R M E A G : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [CommRing E] [Module R E] [CommRing A] [Fintype G]
  {V : G → Type*} [∀ h, AddCommGroup (V h)] [∀ h, Module R (V h)]
  {ρ : A →+* E} {L : M →ₗ[R] E}

/-- Exact beta equality for all colors simultaneously. -/
theorem beta_eq_of_components (row : LiftedRow ρ L) (s : ResidueSection ρ)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G) (hK : ∀ h, h ≠ g → K h ≤ LinearMap.ker (L.comp (embed h)))
    (base : M) {x y : ∀ h, V h} (hown : x g = y g)
    (hcoset : ∀ h, h ≠ g → x h - y h ∈ K h) :
    row.beta s (assemble base embed x) = row.beta s (assemble base embed y) := by
  rw [row.beta_eq_lift_row, row.beta_eq_lift_row]
  exact congrArg s.lift (linear_map_assemble_eq L K embed g hK base hown hcoset)

omit [Fintype G] in
/-- A factor of color g is invariant under translation by any other
color's ambient subspace. -/
theorem beta_add_other_color (row : LiftedRow ρ L) (s : ResidueSection ρ)
    (K : G → Submodule R M) (g : G)
    (hK : ∀ h, h ≠ g → K h ≤ LinearMap.ker L)
    {h : G} (hh : h ≠ g) (x : M) (k : K h) :
    row.beta s (x + k) = row.beta s x :=
  row.beta_add_invariant s (K h) (hK h hh) x k.property

theorem beta_pi_eq [DecidableEq G] {L : (∀ h, V h) →ₗ[R] E}
    (row : LiftedRow ρ L) (s : ResidueSection ρ)
    (K : ∀ h, Submodule R (V h)) (g : G)
    (hK : ∀ h, h ≠ g →
      K h ≤ LinearMap.ker (L.comp (LinearMap.single R V h)))
    {x y : ∀ h, V h} (hown : x g = y g)
    (hcoset : ∀ h, h ≠ g → x h - y h ∈ K h) :
    row.beta s x = row.beta s y := by
  rw [row.beta_eq_lift_row, row.beta_eq_lift_row]
  exact congrArg s.lift (linear_map_pi_eq L K g hK hown hcoset)

/-- Any fixed construction on the beta vector inherits the proved
independence. No invariance premise is imposed on the constructed values. -/
theorem lifted_group_eq_of_components {J B : Type*}
    (rows : J → M →ₗ[R] E) (lifted : ∀ j, LiftedRow ρ (rows j))
    (s : ResidueSection ρ) (build : (J → A) → B)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G)
    (hK : ∀ j h, h ≠ g → K h ≤ LinearMap.ker ((rows j).comp (embed h)))
    (base : M) {x y : ∀ h, V h} (hown : x g = y g)
    (hcoset : ∀ h, h ≠ g → x h - y h ∈ K h) :
    build (fun j => (lifted j).beta s (assemble base embed x)) =
      build (fun j => (lifted j).beta s (assemble base embed y)) := by
  apply congrArg build
  funext j
  exact beta_eq_of_components (lifted j) s K embed g (hK j) base hown hcoset

end Beta

section CosetFibers

variable {R M E A G : Type*} [Field R] [AddCommGroup M] [Module R M]
  [CommRing E] [Module R E] [CommRing A] [Fintype G]
  {V : G → Type*} [∀ h, AddCommGroup (V h)] [∀ h, Module R (V h)]
  {ρ : A →+* E} {L : M →ₗ[R] E}

omit [Fintype G] in
/-- Equal quotient classes provide exactly the component-difference
hypotheses used by the linear argument. -/
theorem cosetFiber_sub_mem (K : ∀ h, Submodule R (V h))
    (q : ∀ h, V h ⧸ K h)
    (x y : ∀ h, CosetCardinality.CosetFiber (K h) (q h)) (h : G) :
    (x h).val - (y h).val ∈ K h :=
  (Submodule.Quotient.eq (K h)).mp ((x h).property.trans (y h).property.symm)

/-- For fixed outer cosets, only the own-color inner point matters. -/
theorem beta_eq_on_coset_fibers (row : LiftedRow ρ L) (s : ResidueSection ρ)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G) (hK : ∀ h, h ≠ g → K h ≤ LinearMap.ker (L.comp (embed h)))
    (base : M) (q : ∀ h, V h ⧸ K h)
    {x y : ∀ h, CosetCardinality.CosetFiber (K h) (q h)} (hown : x g = y g) :
    row.beta s (assemble base embed (fun h => (x h).val)) =
      row.beta s (assemble base embed (fun h => (y h).val)) := by
  apply beta_eq_of_components row s K embed g hK base
  · exact congrArg Subtype.val hown
  · intro h _
    exact cosetFiber_sub_mem K q x y h

end CosetFibers

section ActualSymbolicGroups

variable {R M E A G X F : Type*} [Field R] [AddCommGroup M] [Module R M]
  [CommRing E] [Module R E] [CommRing A] [Fintype G] [Fintype X]
  {V : G → Type*} [∀ h, AddCommGroup (V h)] [∀ h, Module R (V h)]
  {σ : F → Type*} {ρ : A →+* E}

/-- The actual polynomial group from Counting, before truncation, depends
only on its own color coordinate. Its invariance follows from row kernels. -/
theorem rowGroup_eq_of_components
    (factors : Finset F) (table : ∀ e, MvPolynomial (σ e) A)
    (paths : ∀ e, σ e → X → Polynomial A) (θ : A) (radius : ℕ)
    (rows : ∀ e, σ e → M →ₗ[R] E)
    (lifted : ∀ e i, LiftedRow ρ (rows e i)) (s : ResidueSection ρ)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G)
    (hK : ∀ e ∈ factors, ∀ i h, h ≠ g →
      K h ≤ LinearMap.ker ((rows e i).comp (embed h)))
    (base : M) {x y : ∀ h, V h} (hown : x g = y g)
    (hcoset : ∀ h, h ≠ g → x h - y h ∈ K h) :
    Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z) (assemble base embed x) =
      Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z) (assemble base embed y) := by
  apply Counting.rowGroup_congr
  intro e he i
  exact beta_eq_of_components (lifted e i) s K embed g (hK e he i)
    base hown hcoset

/-- The fixed-coset formulation matches the inner tuple used by the
multi-color separated moment sum. -/
theorem rowGroup_eq_on_coset_fibers
    (factors : Finset F) (table : ∀ e, MvPolynomial (σ e) A)
    (paths : ∀ e, σ e → X → Polynomial A) (θ : A) (radius : ℕ)
    (rows : ∀ e, σ e → M →ₗ[R] E)
    (lifted : ∀ e i, LiftedRow ρ (rows e i)) (s : ResidueSection ρ)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G)
    (hK : ∀ e ∈ factors, ∀ i h, h ≠ g →
      K h ≤ LinearMap.ker ((rows e i).comp (embed h)))
    (base : M) (q : ∀ h, V h ⧸ K h)
    {x y : ∀ h, CosetCardinality.CosetFiber (K h) (q h)} (hown : x g = y g) :
    Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z)
        (assemble base embed (fun h => (x h).val)) =
      Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z)
        (assemble base embed (fun h => (y h).val)) := by
  apply rowGroup_eq_of_components factors table paths θ radius rows lifted s
    K embed g hK base
  · exact congrArg Subtype.val hown
  · intro h _
    exact cosetFiber_sub_mem K q x y h

/-- Explicit factorization through the own-color point: all other
components may be replaced with fixed representatives in their cosets. -/
theorem rowGroup_eq_representatives [DecidableEq G]
    (factors : Finset F) (table : ∀ e, MvPolynomial (σ e) A)
    (paths : ∀ e, σ e → X → Polynomial A) (θ : A) (radius : ℕ)
    (rows : ∀ e, σ e → M →ₗ[R] E)
    (lifted : ∀ e i, LiftedRow ρ (rows e i)) (s : ResidueSection ρ)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G)
    (hK : ∀ e ∈ factors, ∀ i h, h ≠ g →
      K h ≤ LinearMap.ker ((rows e i).comp (embed h)))
    (base : M) (q : ∀ h, V h ⧸ K h)
    (x representatives : ∀ h, CosetCardinality.CosetFiber (K h) (q h)) :
    Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z)
        (assemble base embed (fun h => (x h).val)) =
      Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z)
        (assemble base embed
          (fun h => (Function.update representatives g (x g) h).val)) := by
  apply rowGroup_eq_on_coset_fibers factors table paths θ radius rows lifted s
    K embed g hK base q
  simp only [Function.update_self]

/-- The equality survives the manuscript's canonical symbolic truncation. -/
theorem canonical_rowGroup_eq_on_coset_fibers
    (μ D N : ℕ) (factors : Finset F) (table : ∀ e, MvPolynomial (σ e) A)
    (paths : ∀ e, σ e → X → Polynomial A) (θ : A) (radius : ℕ)
    (rows : ∀ e, σ e → M →ₗ[R] E)
    (lifted : ∀ e i, LiftedRow ρ (rows e i)) (s : ResidueSection ρ)
    (K : ∀ h, Submodule R (V h)) (embed : ∀ h, V h →ₗ[R] M)
    (g : G)
    (hK : ∀ e ∈ factors, ∀ i h, h ≠ g →
      K h ≤ LinearMap.ker ((rows e i).comp (embed h)))
    (base : M) (q : ∀ h, V h ⧸ K h)
    {x y : ∀ h, CosetCardinality.CosetFiber (K h) (q h)} (hown : x g = y g) :
    Truncation.canonical μ D N
      (Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z)
        (assemble base embed (fun h => (x h).val))) =
      Truncation.canonical μ D N
      (Counting.rowGroup factors table paths θ radius
        (fun z e i => (lifted e i).beta s z)
        (assemble base embed (fun h => (y h).val))) := by
  exact congrArg (Truncation.canonical μ D N)
    (rowGroup_eq_on_coset_fibers factors table paths θ radius rows lifted s
      K embed g hK base q hown)

end ActualSymbolicGroups

section SupportedCoordinates

variable {R E A I G : Type*} [Field R] [CommRing E] [Module R E] [CommRing A]
  [Fintype I] [DecidableEq I] [Fintype G]

omit [Fintype I] in
/-- A point of a restricted supported subspace returns to that subspace
under actual zero extension. -/
theorem coordinateExtend_restricted_mem (S : Finset I)
    (K : Submodule R (I → R))
    (hK : ∀ x ∈ K, ∀ i, i ∉ S → x i = 0)
    {x : S → R} (hx : x ∈ CosetCardinality.restrictedSubspace S K) :
    SubexpDirectSums.coordinateExtend S x ∈ K := by
  apply CosetCardinality.mem_of_restriction_mem S K hK
  · intro i hi
    exact SubexpDirectSums.coordinateExtend_zero S x i hi
  · have heq :
        (fun i : S => SubexpDirectSums.coordinateExtend S x i.val) = x := by
      funext i
      exact SubexpDirectSums.coordinateExtend_apply S x i.val i.property
    rw [heq]
    exact hx

omit [Fintype I] in
/-- Global layout annihilation implies exactly the local kernel hypothesis
used by the arbitrary-color coset proof. -/
theorem restrictedSubspace_le_ker_coordinateExtend (S : Finset I)
    (K : Submodule R (I → R))
    (hsupport : ∀ x ∈ K, ∀ i, i ∉ S → x i = 0)
    (L : (I → R) →ₗ[R] E) (hK : K ≤ LinearMap.ker L) :
    CosetCardinality.restrictedSubspace S K ≤
      LinearMap.ker (L.comp (SubexpDirectSums.coordinateExtend S)) := by
  intro x hx
  exact hK (coordinateExtend_restricted_mem S K hsupport hx)

/-- Changing one color's point inside its fixed coset changes the actual
ambient reconstruction by a vector of that color's global subspace. -/
theorem coordinateAssemble_sub_mem
    (S : G → Finset I) (K : G → Submodule R (I → R))
    (hsupport : ∀ h x, x ∈ K h → ∀ i, i ∉ S h → x i = 0)
    (base : ↥((Finset.univ.biUnion S)ᶜ) → R)
    (x y : ∀ h, S h → R) (g : G) (hother : ∀ h, h ≠ g → x h = y h)
    (hcoset : x g - y g ∈ CosetCardinality.restrictedSubspace (S g) (K g)) :
    SubexpDirectSums.coordinateAssemble S (base, x) -
      SubexpDirectSums.coordinateAssemble S (base, y) ∈ K g := by
  change assemble
    (SubexpDirectSums.coordinateExtend ((Finset.univ.biUnion S)ᶜ) base)
    (fun h => SubexpDirectSums.coordinateExtend (S h)) x -
    assemble
    (SubexpDirectSums.coordinateExtend ((Finset.univ.biUnion S)ᶜ) base)
    (fun h => SubexpDirectSums.coordinateExtend (S h)) y ∈ K g
  rw [assemble_sub_eq _ _ x y g hother]
  exact coordinateExtend_restricted_mem (S g) (K g) (hsupport g) hcoset

/-- Exact beta invariance for the actual zero-extension reconstruction,
using only supported-subspace and annihilation facts from the layout. -/
theorem beta_coordinateAssemble_eq {ρ : A →+* E} {L : (I → R) →ₗ[R] E}
    (row : LiftedRow ρ L) (s : ResidueSection ρ)
    (S : G → Finset I) (K : G → Submodule R (I → R))
    (hsupport : ∀ h x, x ∈ K h → ∀ i, i ∉ S h → x i = 0)
    (g : G) (hK : ∀ h, h ≠ g → K h ≤ LinearMap.ker L)
    (base : ↥((Finset.univ.biUnion S)ᶜ) → R)
    (q : ∀ h, (S h → R) ⧸ CosetCardinality.restrictedSubspace (S h) (K h))
    {x y : ∀ h, CosetCardinality.CosetFiber
      (CosetCardinality.restrictedSubspace (S h) (K h)) (q h)}
    (hown : x g = y g) :
    row.beta s (SubexpDirectSums.coordinateAssemble S
      (base, fun h => (x h).val)) =
    row.beta s (SubexpDirectSums.coordinateAssemble S
      (base, fun h => (y h).val)) := by
  apply beta_eq_on_coset_fibers row s
    (fun h => CosetCardinality.restrictedSubspace (S h) (K h))
    (fun h => SubexpDirectSums.coordinateExtend (S h)) g
    (fun h hh => restrictedSubspace_le_ker_coordinateExtend
      (S h) (K h) (hsupport h) L (hK h hh))
    (SubexpDirectSums.coordinateExtend ((Finset.univ.biUnion S)ᶜ) base) q hown

/-- Same statement phrased using the inverse of the genuine coordinate
linear equivalence. -/
theorem beta_coordinateSplitEquiv_symm_eq
    {ρ : A →+* E} {L : (I → R) →ₗ[R] E}
    (row : LiftedRow ρ L) (s : ResidueSection ρ)
    (S : G → Finset I) (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : G → Submodule R (I → R))
    (hsupport : ∀ h x, x ∈ K h → ∀ i, i ∉ S h → x i = 0)
    (g : G) (hK : ∀ h, h ≠ g → K h ≤ LinearMap.ker L)
    (base : ↥((Finset.univ.biUnion S)ᶜ) → R)
    (q : ∀ h, (S h → R) ⧸ CosetCardinality.restrictedSubspace (S h) (K h))
    {x y : ∀ h, CosetCardinality.CosetFiber
      (CosetCardinality.restrictedSubspace (S h) (K h)) (q h)}
    (hown : x g = y g) :
    row.beta s ((SubexpDirectSums.coordinateSplitEquiv S hS).symm
      (base, fun h => (x h).val)) =
    row.beta s ((SubexpDirectSums.coordinateSplitEquiv S hS).symm
      (base, fun h => (y h).val)) :=
  beta_coordinateAssemble_eq row s S K hsupport g hK base q hown

/-- The actual symbolic group is exactly independent of the other inner
coset points in the actual ambient coordinate reconstruction. -/
theorem rowGroup_coordinateAssemble_eq
    {F : Type*} {σ : F → Type*} {ρ : A →+* E}
    (factors : Finset F) (table : ∀ e, MvPolynomial (σ e) A)
    (paths : ∀ e, σ e → I → Polynomial A) (θ : A) (radius : ℕ)
    (rows : ∀ e, σ e → (I → R) →ₗ[R] E)
    (lifted : ∀ e i, LiftedRow ρ (rows e i)) (s : ResidueSection ρ)
    (S : G → Finset I) (K : G → Submodule R (I → R))
    (hsupport : ∀ h x, x ∈ K h → ∀ i, i ∉ S h → x i = 0)
    (g : G)
    (hK : ∀ e ∈ factors, ∀ i h, h ≠ g → K h ≤ LinearMap.ker (rows e i))
    (base : ↥((Finset.univ.biUnion S)ᶜ) → R)
    (q : ∀ h, (S h → R) ⧸ CosetCardinality.restrictedSubspace (S h) (K h))
    {x y : ∀ h, CosetCardinality.CosetFiber
      (CosetCardinality.restrictedSubspace (S h) (K h)) (q h)}
    (hown : x g = y g) :
    Counting.rowGroup factors table paths θ radius
      (fun z e i => (lifted e i).beta s z)
      (SubexpDirectSums.coordinateAssemble S (base, fun h => (x h).val)) =
    Counting.rowGroup factors table paths θ radius
      (fun z e i => (lifted e i).beta s z)
      (SubexpDirectSums.coordinateAssemble S (base, fun h => (y h).val)) := by
  apply Counting.rowGroup_congr
  intro e he i
  exact beta_coordinateAssemble_eq (lifted e i) s S K hsupport g (hK e he i)
    base q hown

end SupportedCoordinates

end SubexponentialSAT.SubexpInvariance

end OAI.Algorithms
