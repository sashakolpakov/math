import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Reconstruction from formal polynomial jets over a commutative ring

These results use unit differences of nodes, not a field assumption. Jets are
formal Taylor polynomials modulo `X ^ D`; no factorial divisions occur.
-/

noncomputable section

namespace SubexponentialSAT.JetCRT

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- The local modulus for an order-`D` jet at `a`. -/
def nodePower (a : A) (D : ℕ) : A[X] := (X - C a) ^ D

/-- The ideal of polynomials whose order-`D` jet vanishes at `a`. -/
def nodeIdeal (a : A) (D : ℕ) : Ideal A[X] := Ideal.span {nodePower a D}

/-- The formal order-`D` Taylor polynomial, using `X` as the local coordinate. -/
noncomputable def jet (a : A) (D : ℕ) (f : A[X]) : A[X] :=
  (f.comp (X + C a)) %ₘ (X ^ D)

theorem nodePower_monic (a : A) (D : ℕ) : (nodePower a D).Monic :=
  (monic_X_sub_C a).pow D

theorem nodePower_coprime {a b : A} (D E : ℕ) (h : IsUnit (a - b)) :
    IsCoprime (nodePower a D) (nodePower b E) :=
  (isCoprime_X_sub_C_of_isUnit_sub h).pow

theorem nodeIdeal_sup_eq_top {a b : A} (D E : ℕ) (h : IsUnit (a - b)) :
    nodeIdeal a D ⊔ nodeIdeal b E = ⊤ :=
  (Ideal.sup_eq_top_iff_isCoprime _ _).2 (nodePower_coprime D E h)

theorem nodeIdeal_coprime {a b : A} (D E : ℕ) (h : IsUnit (a - b)) :
    IsCoprime (nodeIdeal a D) (nodeIdeal b E) :=
  (Ideal.isCoprime_span_singleton_iff _ _).2 (nodePower_coprime D E h)

theorem jet_eq_iff_dvd_sub (a : A) (D : ℕ) (f g : A[X]) :
    jet a D f = jet a D g ↔ nodePower a D ∣ f - g := by
  change (f.comp (X + C a)) %ₘ (X ^ D) = (g.comp (X + C a)) %ₘ (X ^ D) ↔ _
  rw [← sub_eq_zero, ← sub_modByMonic, ← sub_comp,
    modByMonic_eq_zero_iff_dvd (monic_X.pow D),
    dvd_comp_X_add_C_iff]
  simp only [nodePower, pow_comp, X_comp]

theorem jet_eq_iff_coeff (a : A) (D : ℕ) (f g : A[X]) :
    jet a D f = jet a D g ↔
      ∀ n < D, (f.comp (X + C a)).coeff n = (g.comp (X + C a)).coeff n := by
  change (f.comp (X + C a)) %ₘ (X ^ D) = (g.comp (X + C a)) %ₘ (X ^ D) ↔ _
  rw [← sub_eq_zero, ← sub_modByMonic,
    modByMonic_eq_zero_iff_dvd (monic_X.pow D), X_pow_dvd_iff]
  simp only [coeff_sub, sub_eq_zero]

variable {ι : Type*} [Fintype ι]

/-- The product of all powered linear local moduli. -/
def modulus (θ : ι → A) (D : ℕ) : A[X] := ∏ i, nodePower (θ i) D

theorem modulus_monic (θ : ι → A) (D : ℕ) : (modulus θ D).Monic :=
  monic_prod_of_monic _ _ (fun i _ => nodePower_monic (θ i) D)

theorem modulus_natDegree [Nontrivial A] (θ : ι → A) (D : ℕ) :
    (modulus θ D).natDegree = Fintype.card ι * D := by
  rw [modulus, natDegree_prod_of_monic _ _ (fun i _ => nodePower_monic (θ i) D)]
  simp only [nodePower, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  simp

theorem modulus_degree [Nontrivial A] (θ : ι → A) (D : ℕ) :
    (modulus θ D).degree = (Fintype.card ι * D : ℕ) := by
  rw [degree_eq_natDegree (modulus_monic θ D).ne_zero, modulus_natDegree]

theorem modulus_dvd_iff (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (f : A[X]) :
    modulus θ D ∣ f ↔ ∀ i, nodePower (θ i) D ∣ f := by
  classical
  constructor
  · intro h i
    have hi : nodePower (θ i) D ∣ ∏ j, nodePower (θ j) D :=
      Finset.dvd_prod_of_mem (fun j => nodePower (θ j) D) (Finset.mem_univ i)
    exact hi.trans h
  · intro h
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact nodePower_coprime D D (hθ hij)
    · exact h

theorem nodeIdeal_iInf (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) :
    (⨅ i, nodeIdeal (θ i) D) = Ideal.span {modulus θ D} := by
  exact Ideal.iInf_span_singleton (fun i j hij => nodePower_coprime D D (hθ hij))

/-- Divisibility at all nodes determines a polynomial below the total degree. -/
theorem eq_of_dvd_sub_of_degree_lt (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (f g : A[X])
    (hf : f.degree < (Fintype.card ι * D : ℕ))
    (hg : g.degree < (Fintype.card ι * D : ℕ))
    (hlocal : ∀ i, nodePower (θ i) D ∣ f - g) : f = g := by
  nontriviality A
  apply sub_eq_zero.mp
  by_contra hfg
  have hdiv := (modulus_dvd_iff θ D hθ (f - g)).2 hlocal
  have hdeg : (f - g).degree < (modulus θ D).degree := by
    rw [modulus_degree]
    exact (degree_sub_le f g).trans_lt (max_lt hf hg)
  exact (modulus_monic θ D).not_dvd_of_degree_lt hfg hdeg hdiv

/-- Actual truncated formal Taylor polynomials determine the global polynomial. -/
theorem eq_of_jets_of_degree_lt (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (f g : A[X])
    (hf : f.degree < (Fintype.card ι * D : ℕ))
    (hg : g.degree < (Fintype.card ι * D : ℕ))
    (hjets : ∀ i, jet (θ i) D f = jet (θ i) D g) : f = g := by
  exact eq_of_dvd_sub_of_degree_lt θ D hθ f g hf hg
    (fun i => (jet_eq_iff_dvd_sub (θ i) D f g).1 (hjets i))

/-- The natural-degree form is convenient for bounds on the global count polynomial. -/
theorem eq_of_jets_of_natDegree_lt (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (f g : A[X])
    (hf : f.natDegree < Fintype.card ι * D)
    (hg : g.natDegree < Fintype.card ι * D)
    (hjets : ∀ i, jet (θ i) D f = jet (θ i) D g) : f = g := by
  exact eq_of_jets_of_degree_lt θ D hθ f g
    (degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hf))
    (degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hg)) hjets

/-- CRT followed by monic division supplies the unique bounded-degree representative
of any family of local polynomial residues. This is an existence theorem, not a
claim about computability or bit complexity. -/
theorem exists_unique_representative [Nontrivial A] (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (residues : ι → A[X]) :
    ∃! f : A[X], f.degree < (Fintype.card ι * D : ℕ) ∧
      ∀ i, nodePower (θ i) D ∣ f - residues i := by
  classical
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal
    (I := fun i => nodeIdeal (θ i) D)
    (fun i j hij => nodeIdeal_coprime D D (hθ hij)) residues
  let r := p %ₘ modulus θ D
  have hr_degree : r.degree < (Fintype.card ι * D : ℕ) := by
    rw [← modulus_degree θ D]
    exact degree_modByMonic_lt p (modulus_monic θ D)
  have hr_mod : modulus θ D ∣ r - p := by
    dsimp [r]
    rw [modByMonic_eq_sub_mul_div,
      sub_right_comm, sub_self, zero_sub]
    exact dvd_neg.mpr (dvd_mul_right _ _)
  have hr_local : ∀ i, nodePower (θ i) D ∣ r - residues i := by
    intro i
    have hpi : nodePower (θ i) D ∣ p - residues i :=
      Ideal.mem_span_singleton.mp (hp i)
    have hri := (modulus_dvd_iff θ D hθ (r - p)).1 hr_mod i
    simpa only [sub_add_sub_cancel] using dvd_add hri hpi
  refine ⟨r, ⟨hr_degree, hr_local⟩, ?_⟩
  intro q hq
  apply eq_of_dvd_sub_of_degree_lt θ D hθ q r hq.1 hr_degree
  intro i
  simpa only [sub_sub_sub_cancel_right] using dvd_sub (hq.2 i) (hr_local i)

/-- Shifting a local polynomial back to the global coordinate and then taking
its jet recovers exactly its truncation. -/
theorem jet_unshift (a : A) (D : ℕ) (f : A[X]) :
    jet a D (f.comp (X - C a)) = f %ₘ (X ^ D) := by
  simp only [jet, comp_assoc, sub_comp, X_comp, C_comp, add_sub_cancel_right, comp_X]

/-- Every family of formal truncated local expansions has a unique global
polynomial of degree below the sum of the local orders. -/
theorem exists_unique_of_jets [Nontrivial A] (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (J : ι → A[X]) :
    ∃! f : A[X], f.degree < (Fintype.card ι * D : ℕ) ∧
      ∀ i, jet (θ i) D f = J i %ₘ (X ^ D) := by
  obtain ⟨f, ⟨hf, hlocal⟩, _⟩ := exists_unique_representative θ D hθ
    (fun i => (J i).comp (X - C (θ i)))
  have hjets : ∀ i, jet (θ i) D f = J i %ₘ (X ^ D) := by
    intro i
    rw [← jet_unshift (θ i) D (J i)]
    exact (jet_eq_iff_dvd_sub (θ i) D _ _).2 (hlocal i)
  refine ⟨f, ⟨hf, hjets⟩, ?_⟩
  intro g hg
  exact eq_of_jets_of_degree_lt θ D hθ g f hg.1 hf
    (fun i => (hg.2 i).trans (hjets i).symm)

section ExplicitFormula

variable [DecidableEq ι]

/-- The product of all local moduli except the one at index `i`. -/
def cofactor (θ : ι → A) (D : ℕ) (i : ι) : A[X] :=
  ∏ j ∈ Finset.univ.erase i, nodePower (θ j) D

theorem cofactor_coprime (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (i : ι) :
    IsCoprime (nodePower (θ i) D) (cofactor θ D i) := by
  apply IsCoprime.prod_right
  intro j hj
  exact nodePower_coprime D D (hθ (Finset.mem_erase.mp hj).1.symm)

theorem nodePower_dvd_cofactor (θ : ι → A) (D : ℕ) {i j : ι} (hij : i ≠ j) :
    nodePower (θ i) D ∣ cofactor θ D j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

/-- Unit-separated nodes provide Bézout certificates for the explicit formula. -/
theorem exists_bezoutCoefficients (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) :
    ∃ u v : ι → A[X], ∀ i,
      u i * cofactor θ D i + v i * nodePower (θ i) D = 1 := by
  have h : ∀ i, ∃ u v : A[X],
      u * cofactor θ D i + v * nodePower (θ i) D = 1 := by
    intro i
    exact (cofactor_coprime θ D hθ i).symm
  choose u v h using h
  exact ⟨u, v, h⟩

/-- A finite-sum CRT formula followed by monic reduction. Its Bézout coefficients
are explicit input data; producing those coefficients efficiently is separate. -/
def reconstructWithBezout (θ : ι → A) (D : ℕ) (u residues : ι → A[X]) : A[X] :=
  (∑ i, u i * cofactor θ D i * residues i) %ₘ modulus θ D

theorem bezoutSum_dvd_sub (θ : ι → A) (D : ℕ) (u v residues : ι → A[X])
    (hbez : ∀ i, u i * cofactor θ D i + v i * nodePower (θ i) D = 1) (i : ι) :
    nodePower (θ i) D ∣ (∑ j, u j * cofactor θ D j * residues j) - residues i := by
  have hdiag : nodePower (θ i) D ∣ u i * cofactor θ D i - 1 := by
    rw [← hbez i, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact dvd_neg.mpr (dvd_mul_left _ _)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_assoc]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right
        (nodePower_dvd_cofactor θ D (Finset.mem_erase.mp hj).1.symm) _) _
  · have h := dvd_mul_of_dvd_left hdiag (residues i)
    simpa only [sub_mul, one_mul] using h

/-- Correctness of the explicit CRT formula, over a commutative ring. No field
operations or derivative/factorial expressions enter this certificate. -/
theorem reconstructWithBezout_spec [Nontrivial A] (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (u v residues : ι → A[X])
    (hbez : ∀ i, u i * cofactor θ D i + v i * nodePower (θ i) D = 1) :
    (reconstructWithBezout θ D u residues).degree < (Fintype.card ι * D : ℕ) ∧
      ∀ i, nodePower (θ i) D ∣ reconstructWithBezout θ D u residues - residues i := by
  let p := ∑ i, u i * cofactor θ D i * residues i
  constructor
  · rw [← modulus_degree θ D]
    exact degree_modByMonic_lt p (modulus_monic θ D)
  · intro i
    have hmod : modulus θ D ∣ reconstructWithBezout θ D u residues - p := by
      change modulus θ D ∣ p %ₘ modulus θ D - p
      rw [modByMonic_eq_sub_mul_div,
        sub_right_comm, sub_self, zero_sub]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    have hi := (modulus_dvd_iff θ D hθ _).1 hmod i
    simpa only [p, sub_add_sub_cancel] using
      dvd_add hi (bezoutSum_dvd_sub θ D u v residues hbez i)

/-- The explicit formula with inputs expressed in their local coordinates. -/
def reconstructJetsWithBezout (θ : ι → A) (D : ℕ) (u J : ι → A[X]) : A[X] :=
  reconstructWithBezout θ D u (fun i => (J i).comp (X - C (θ i)))

theorem reconstructJetsWithBezout_spec [Nontrivial A] (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (u v J : ι → A[X])
    (hbez : ∀ i, u i * cofactor θ D i + v i * nodePower (θ i) D = 1) :
    (reconstructJetsWithBezout θ D u J).degree < (Fintype.card ι * D : ℕ) ∧
      ∀ i, jet (θ i) D (reconstructJetsWithBezout θ D u J) = J i %ₘ (X ^ D) := by
  obtain ⟨hdegree, hlocal⟩ := reconstructWithBezout_spec θ D hθ u v
    (fun i => (J i).comp (X - C (θ i))) hbez
  refine ⟨hdegree, ?_⟩
  intro i
  rw [← jet_unshift (θ i) D (J i)]
  exact (jet_eq_iff_dvd_sub (θ i) D _ _).2 (hlocal i)

/-- Applying the certified finite-sum formula to the correct local data recovers
the original polynomial under its degree bound. -/
theorem reconstructJetsWithBezout_eq [Nontrivial A] (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (u v J : ι → A[X])
    (hbez : ∀ i, u i * cofactor θ D i + v i * nodePower (θ i) D = 1)
    (H : A[X]) (hdegree : H.degree < (Fintype.card ι * D : ℕ))
    (hJ : ∀ i, jet (θ i) D H = J i %ₘ (X ^ D)) :
    reconstructJetsWithBezout θ D u J = H := by
  obtain ⟨hdegree', hjets⟩ := reconstructJetsWithBezout_spec θ D hθ u v J hbez
  exact eq_of_jets_of_degree_lt θ D hθ _ H hdegree' hdegree
    (fun i => (hjets i).trans (hJ i).symm)

end ExplicitFormula

end SubexponentialSAT.JetCRT

end

end OAI.Algorithms
