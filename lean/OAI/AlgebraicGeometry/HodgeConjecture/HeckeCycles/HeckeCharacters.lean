import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent

/-! # Hecke Characters -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

/-!
# Constructing CMExtraction's projectors from the Commuting decomposition

The projectors are the coordinate maps of the internal direct sum, not
extra supplied data. Their Hodge compatibility is derived from the actual
operators preserving both Hodge pieces. Restricting the finite index set
to summands occurring in theta vectors constructs the active decomposition.
-/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent.CM

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq I]

/-- The coordinate projector associated to an internal direct sum. -/
def projector (S : I → Submodule K V) (hS : DirectSum.IsInternal S) (i : I) :
    Module.End K V :=
  (S i).subtype.comp ((DirectSum.component K I (fun j => S j) i).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hS).symm.toLinearMap)

theorem projector_mem (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (i : I) (x : V) : projector S hS i x ∈ S i :=
  ((LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hS).symm x i).property

theorem projector_of_mem (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (i : I) {x : V} (hx : x ∈ S i) : projector S hS i x = x := by
  change ((LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hS).symm x i : V) = x
  rw [hS.ofBijective_coeLinearMap_of_mem hx]

theorem projector_of_mem_ne (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    {i j : I} (hij : j ≠ i) {x : V} (hx : x ∈ S j) : projector S hS i x = 0 := by
  change ((LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hS).symm x i : V) = 0
  rw [hS.ofBijective_coeLinearMap_of_mem_ne hij hx]
  rfl

theorem projector_idempotent (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (i : I) : (projector S hS i).comp (projector S hS i) = projector S hS i := by
  ext x
  exact projector_of_mem S hS i (projector_mem S hS i x)

theorem projector_mul_ne (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    {i j : I} (hji : j ≠ i) : projector S hS i * projector S hS j = 0 := by
  ext x
  exact projector_of_mem_ne S hS hji (projector_mem S hS j x)

theorem projector_range (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (i : I) : LinearMap.range (projector S hS i) = S i := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact projector_mem S hS i x
  · intro x hx
    exact ⟨x, projector_of_mem S hS i hx⟩

theorem sum_projector [Fintype I] (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (x : V) : ∑ i, projector S hS i x = x := by
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hS
  calc
    _ = DirectSum.coeLinearMap S
        (∑ i, DirectSum.of (fun j => S j) i (e.symm x i)) := by
      simp only [map_sum, DirectSum.coeLinearMap_of]
      rfl
    _ = DirectSum.coeLinearMap S (e.symm x) := by
      congr 1
      simpa using DirectSum.sum_univ_of (e.symm x)
    _ = x := e.apply_symm_apply x

/-- Every operator preserving each summand commutes with its coordinate projectors. -/
theorem projector_commutes [Fintype I] (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (T : Module.End K V) (hT : ∀ i x, x ∈ S i → T x ∈ S i) (i : I) :
    Commute (projector S hS i) T := by
  apply LinearMap.ext
  intro x
  change projector S hS i (T x) = T (projector S hS i x)
  calc
    _ = projector S hS i (T (∑ j, projector S hS j x)) := by
      rw [sum_projector]
    _ = ∑ j, projector S hS i (T (projector S hS j x)) := by
      simp only [map_sum]
    _ = projector S hS i (T (projector S hS i x)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact projector_of_mem_ne S hS hji (hT j _ (projector_mem S hS j x))
      · simp
    _ = T (projector S hS i x) :=
      projector_of_mem S hS i (hT i _ (projector_mem S hS i x))

def jointSpace {J : Type*} (T : J → Module.End K V) (χ : J → K) : Submodule K V :=
  ⨅ j, (T j).genEigenspace (χ j) ⊤

/-- The independence and spanning clauses of Commuting give the internal
decomposition after zero summands are removed. Commuting's finiteness clause
then supplies a Fintype instance for this very index set. -/
theorem joint_internal_of_Commuting {J : Type*}
    (T : J → Module.End K V)
    (h_Commuting_independent : iSupIndep (jointSpace T))
    (h_Commuting_span : (⨆ χ, jointSpace T χ) = ⊤) :
    DirectSum.IsInternal
      (fun χ : {χ : J → K // jointSpace T χ ≠ ⊥} => jointSpace T χ.val) :=
  DirectSum.isInternal_ne_bot_iff.mpr
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      h_Commuting_independent h_Commuting_span)

/-- Commuting's relevant clauses follow from the existing simultaneous generalized
eigenspace theorems; no diagonalizability assumption is needed. -/
theorem joint_finite_and_internal [IsAlgClosed K] [FiniteDimensional K V]
    {J : Type*} (T : J → Module.End K V)
    (hcomm : ∀ j k, Commute (T j) (T k)) :
    Set.Finite {χ : J → K | jointSpace T χ ≠ ⊥} ∧
      DirectSum.IsInternal
        (fun χ : {χ : J → K // jointSpace T χ ≠ ⊥} => jointSpace T χ.val) := by
  have hi : iSupIndep (jointSpace T) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
      (fun i j => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i).eq)
  have hs : (⨆ χ, jointSpace T χ) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      T (fun i j _ => hcomm i j) (fun i => (T i).iSup_maxGenEigenspace_eq_top)
  exact ⟨Submodule.finite_ne_bot_of_iSupIndep hi, joint_internal_of_Commuting T hi hs⟩

theorem jointSpace_stable_of_commutes {J : Type*}
    (T : J → Module.End K V) (χ : J → K) (Q : Module.End K V)
    (hQ : ∀ j, Commute (T j) Q) {x : V} (hx : x ∈ jointSpace T χ) :
    Q x ∈ jointSpace T χ := by
  simp only [jointSpace, Submodule.mem_iInf] at hx ⊢
  intro j
  exact Module.End.mapsTo_genEigenspace_of_comm (hQ j) (χ j) ⊤ (hx j)

/-- Different joint characters have disjoint generalized eigenspaces. -/
theorem jointSpace_disjoint {J : Type*} (T : J → Module.End K V)
    {χ ψ : J → K} (hne : χ ≠ ψ) : Disjoint (jointSpace T χ) (jointSpace T ψ) := by
  have hex : ∃ j, χ j ≠ ψ j := by
    by_contra h
    apply hne
    funext j
    exact not_ne_iff.mp (fun hj => h ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hex
  exact ((T j).disjoint_genEigenspace hj ⊤ ⊤).mono
    (iInf_le (fun k => (T k).genEigenspace (χ k) ⊤) j)
    (iInf_le (fun k => (T k).genEigenspace (ψ k) ⊤) j)

omit [DecidableEq I] in
/-- A finite spectral decomposition that spans the ambient space contains
the whole joint eigenspaces, not just unspecified subspaces of them. -/
theorem ranges_eq_jointSpaces [Fintype I] {J : Type*}
    (T : J → Module.End K V) (χ : I → J → K)
    (hχ : Function.Injective χ) (P : I → Module.End K V)
    (hspan : ∀ x, ∑ i, P i x = x)
    (hrange : ∀ i, LinearMap.range (P i) ≤ jointSpace T (χ i))
    (hcomm : ∀ i j, Commute (P i) (T j)) :
    ∀ i, LinearMap.range (P i) = jointSpace T (χ i) := by
  intro i
  apply le_antisymm (hrange i)
  intro x hx
  have hother : ∀ j, j ≠ i → P j x = 0 := by
    intro j hji
    have hj := hrange j (LinearMap.mem_range_self (P j) x)
    have hi := jointSpace_stable_of_commutes T (χ i) (P j)
      (fun k => (hcomm j k).symm) hx
    exact Submodule.disjoint_def.mp (jointSpace_disjoint T (hχ.ne hji)) _ hj hi
  have heq : ∑ j, P j x = P i x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact hother j hji
    · simp
  exact ⟨x, heq.symm.trans (hspan x)⟩

/-- Characterize the coordinate projector by its action on every summand. -/
theorem projector_unique [Fintype I]
    (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (i : I) (Q : Module.End K V)
    (hself : ∀ x ∈ S i, Q x = x)
    (hother : ∀ j, j ≠ i → ∀ x ∈ S j, Q x = 0) :
    Q = projector S hS i := by
  apply LinearMap.ext
  intro x
  calc
    Q x = Q (∑ j, projector S hS j x) := by rw [sum_projector]
    _ = ∑ j, Q (projector S hS j x) := map_sum _ _ _
    _ = Q (projector S hS i x) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hother j hji _ (projector_mem S hS j x)
      · simp
    _ = projector S hS i x := hself _ (projector_mem S hS i x)

section Hodge

variable {U J : Type*} [AddCommGroup U] [Module ℚ U]

/-- Spectral projectors preserve Hodge type because the Hecke operators do. -/
theorem joint_projector_hodge [Fintype I]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (T : J → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U))
    (χ : I → J → ℂ)
    (h_Commuting : DirectSum.IsInternal (fun i => jointSpace T (χ i)))
    (hT : ∀ j, T j ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) (i : I) :
    projector (fun j => jointSpace T (χ j)) h_Commuting i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H := by
  let Q := H.holomorphic.projection H.antiholomorphic H.complementary
  have hQid : IsIdempotentElem Q :=
    Submodule.isIdempotentElem_projection H.complementary
  have hQT : ∀ j, Commute Q (T j) := by
    intro j
    apply (LinearMap.IsIdempotentElem.commute_iff hQid).mpr
    rw [Submodule.range_projection, Submodule.ker_projection]
    exact hT j
  have hstable : ∀ j x, x ∈ jointSpace T (χ j) → Q x ∈ jointSpace T (χ j) := by
    intro j x hx
    exact jointSpace_stable_of_commutes T (χ j) Q (fun k => (hQT k).symm) hx
  have hc := (projector_commutes (fun j => jointSpace T (χ j)) h_Commuting Q hstable i).symm
  have hpreserves := (LinearMap.IsIdempotentElem.commute_iff hQid).mp hc
  rw [Submodule.range_projection, Submodule.ker_projection] at hpreserves
  exact hpreserves

end Hodge

/-- The active set is selected by actual nonzero components of theta classes. -/
def Active {Φ : Type*} (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (theta : Φ → V) := {i : I // ∃ φ, projector S hS i (theta φ) ≠ 0}

instance [Fintype I] {Φ : Type*} (S : I → Submodule K V) (hS : DirectSum.IsInternal S)
    (theta : Φ → V) : Fintype (Active S hS theta) := by
  unfold Active
  infer_instance

theorem active_occurs {Φ : Type*} (S : I → Submodule K V)
    (hS : DirectSum.IsInternal S) (theta : Φ → V) (i : Active S hS theta) :
    ∃ φ, projector S hS i.val (theta φ) ≠ 0 := i.property

/-- Discarding unused spectral summands preserves the actual theta decomposition. -/
theorem sum_active_projector [Fintype I] {Φ : Type*} (S : I → Submodule K V)
    (hS : DirectSum.IsInternal S) (theta : Φ → V) (φ : Φ) :
    ∑ i : Active S hS theta, projector S hS i.val (theta φ) = theta φ := by
  calc
    _ = ∑ i, projector S hS i (theta φ) := by
      symm
      apply Finset.sum_congr_set
        {i : I | ∃ ψ, projector S hS i (theta ψ) ≠ 0}
        (fun i => projector S hS i (theta φ))
        (fun i => projector S hS i.val (theta φ))
      · intro i hi
        rfl
      · intro i hi
        by_contra hn
        exact hi ⟨φ, hn⟩
    _ = theta φ := sum_projector S hS (theta φ)

/-- Construct the finite active projectors of an actual rational Hecke action.
The hypotheses concern only the original commuting operators and Hodge
compatibility; every projector and the theta decomposition are conclusions. -/
theorem construct_rational_hecke_projectors
    {U J Φ : Type*} [AddCommGroup U] [Module ℚ U]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (T : J → Module.End ℚ U)
    (hcomm : ∀ j k, Commute (T j) (T k))
    (hHodge : ∀ j, ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (T j))
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification U) :
    ∃ (n : ℕ) (P : Fin n → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U)),
      (∀ i, (P i).comp (P i) = P i) ∧
      (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) ∧
      (∀ i, ∃ φ, P i (theta φ) ≠ 0) ∧
      (∀ φ, ∑ i, P i (theta φ) = theta φ) ∧
      (∀ i, ∃ χ : J → ℂ,
        LinearMap.range (P i) = jointSpace (fun j => (T j).baseChange ℂ) χ) := by
  let : FiniteDimensional ℚ U := H.finiteDimensional
  let TC : J → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U) := fun j => (T j).baseChange ℂ
  have hTC : ∀ j k, Commute (TC j) (TC k) := by
    intro j k
    change (T j).baseChange ℂ * (T k).baseChange ℂ =
      (T k).baseChange ℂ * (T j).baseChange ℂ
    simpa only [LinearMap.baseChange_mul] using
      congrArg (fun f : Module.End ℚ U => f.baseChange ℂ) (hcomm j k).eq
  obtain ⟨hfinite, hinternal⟩ := joint_finite_and_internal TC hTC
  let Spectrum := {χ : J → ℂ // jointSpace TC χ ≠ ⊥}
  let : Fintype Spectrum := hfinite.fintype
  let S : Spectrum → Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification U) := fun χ => jointSpace TC χ.val
  have hinternal' : DirectSum.IsInternal S :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      hinternal.submodule_iSupIndep hinternal.submodule_iSup_eq_top
  let A := Active S hinternal' theta
  let e := Fintype.equivFin A
  let P : Fin (Fintype.card A) → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U) :=
    fun i => projector S hinternal' (e.symm i).val
  refine ⟨Fintype.card A, P, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact projector_idempotent S hinternal' (e.symm i).val
  · intro i
    exact joint_projector_hodge H TC (fun χ : Spectrum => χ.val) hinternal'
      (fun j => (ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff H H (T j)).mpr (hHodge j))
      (e.symm i).val
  · intro i
    exact active_occurs S hinternal' theta (e.symm i)
  · intro φ
    calc
      _ = ∑ i : A, projector S hinternal' i.val (theta φ) :=
        Equiv.sum_comp e.symm (fun i : A => projector S hinternal' i.val (theta φ))
      _ = theta φ := sum_active_projector S hinternal' theta φ
  · intro i
    exact ⟨(e.symm i).val.val, projector_range S hinternal' (e.symm i).val⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM

/-! Nonzero joint generalized eigenspaces of a commutative algebra action
carry actual algebra characters. Multiplicativity follows from commuting
generalized eigenvectors; it is not an additional spectral hypothesis. -/

open _root_.Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem zero_genEigenspace_le_mul (f g : Module.End K V) (h : Commute f g)
    (k : ℕ∞) : f.genEigenspace 0 k ≤ (g * f).genEigenspace 0 k := by
  intro x hx
  simp only [mem_genEigenspace, zero_smul, sub_zero, LinearMap.mem_ker] at hx ⊢
  obtain ⟨n, hn, hx⟩ := hx
  refine ⟨n, hn, ?_⟩
  rw [h.symm.mul_pow, Module.End.mul_apply, hx, map_zero]

theorem genEigenspace_inf_le_mul (f g : Module.End K V) (μ ν : K)
    (h : Commute f g) :
    f.genEigenspace μ ⊤ ⊓ g.genEigenspace ν ⊤ ≤
      (f * g).genEigenspace (μ * ν) ⊤ := by
  let a := g * (f - μ • 1)
  let b := μ • (g - ν • 1)
  have hfg : Commute (f - μ • 1) g :=
    h.sub_left (Algebra.commute_algebraMap_left μ g)
  have ha : f.genEigenspace μ ⊤ ≤ a.genEigenspace 0 ⊤ := by
    have hz : f.genEigenspace μ ⊤ = (f - μ • 1).genEigenspace 0 ⊤ := by
      simp only [Module.End.genEigenspace, zero_smul, sub_zero]
    rw [hz]
    exact zero_genEigenspace_le_mul _ _ hfg ⊤
  have hb : g.genEigenspace ν ⊤ ≤ b.genEigenspace 0 ⊤ := by
    have hz : g.genEigenspace ν ⊤ = (g - ν • 1).genEigenspace 0 ⊤ := by
      simp only [Module.End.genEigenspace, zero_smul, sub_zero]
    rw [hz]
    simpa only [mul_zero] using genEigenspace_le_smul (g - ν • 1) 0 μ ⊤
  have hab : Commute a b := by
    exact ((Commute.refl g).mul_left hfg).sub_right
      (Algebra.commute_algebraMap_right ν a) |>.smul_right μ
  have heq : a + b = f * g - (μ * ν) • 1 := by
    dsimp [a, b]
    rw [mul_sub, smul_sub, mul_smul_comm, mul_one, smul_smul, h.eq.symm]
    abel
  have hadd := genEigenspace_inf_le_add a b 0 0 ⊤ ⊤ hab
  have hshift : (f * g - (μ * ν) • 1).genEigenspace 0 ⊤ =
      (f * g).genEigenspace (μ * ν) ⊤ := by
    simp only [Module.End.genEigenspace, zero_smul, sub_zero]
  simpa only [zero_add, top_add, heq, hshift] using
    (inf_le_inf ha hb).trans hadd

variable {H : Type*} [CommRing H]

theorem character_scalar (T : H →+* Module.End K V) (χ : H → K)
    (hχ : Projectors.jointSpace T χ ≠ ⊥)
    (a : H) (c : K) (ha : T a = c • 1) : χ a = c := by
  by_contra hne
  have ht : (T a).genEigenspace c ⊤ = ⊤ := by
    rw [ha]
    apply top_unique
    intro x _
    simp only [mem_genEigenspace, sub_self, LinearMap.mem_ker]
    exact ⟨1, le_top, by simp⟩
  apply hχ
  apply eq_bot_iff.mpr
  have hd := (T a).disjoint_genEigenspace hne ⊤ ⊤
  rw [ht, disjoint_top] at hd
  exact (iInf_le (fun h => (T h).genEigenspace (χ h) ⊤) a).trans hd.le

theorem character_mul (T : H →+* Module.End K V) (χ : H → K)
    (hχ : Projectors.jointSpace T χ ≠ ⊥) (a b : H) :
    χ (a * b) = χ a * χ b := by
  by_contra hne
  have hcomm : Commute (T a) (T b) := (Commute.all a b).map T
  have hle : Projectors.jointSpace T χ ≤
      (T (a * b)).genEigenspace (χ a * χ b) ⊤ := by
    rw [map_mul]
    exact (le_inf (iInf_le _ a) (iInf_le _ b)).trans
      (genEigenspace_inf_le_mul _ _ _ _ hcomm)
  apply hχ
  apply eq_bot_iff.mpr
  exact (le_inf (iInf_le _ (a * b)) hle).trans
    ((T (a * b)).disjoint_genEigenspace hne ⊤ ⊤).le_bot

/-- The same function used to index the joint spaces is a ring character. -/
def jointRingCharacter (T : H →+* Module.End K V) (χ : H → K)
    (hχ : Projectors.jointSpace T χ ≠ ⊥) : H →+* K where
  toFun := χ
  map_one' := character_scalar T χ hχ 1 1 (by simp)
  map_mul' := character_mul T χ hχ
  map_zero' := character_scalar T χ hχ 0 0 (by simp)
  map_add' := map_add_of_iInf_genEigenspace_ne_bot_of_commute T χ ⊤ hχ
    (fun a b => (Commute.all a b).map T)

/-- Rational Hecke characters satisfy the exact algebra-homomorphism
interface required by GeometricComparison, without changing the original eigenvalues. -/
def jointCharacter [Algebra ℚ H] [CharZero K]
    (T : H →+* Module.End K V) (χ : H → K)
    (hχ : Projectors.jointSpace T χ ≠ ⊥) : H →ₐ[ℚ] K :=
  (jointRingCharacter T χ hχ).toRatAlgHom

theorem jointCharacter_apply [Algebra ℚ H] [CharZero K]
    (T : H →+* Module.End K V) (χ : H → K)
    (hχ : Projectors.jointSpace T χ ≠ ⊥) (h : H) :
    jointCharacter T χ hχ h = χ h := rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM

end

end OAI
