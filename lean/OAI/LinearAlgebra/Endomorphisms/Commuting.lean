import Mathlib

/-! # Commuting -/

namespace OAI.LinearAlgebra.Endomorphisms.Commuting.Construction

/-!
# Commuting: commuting endomorphisms

This file proves the specification independently of `Statements.Commuting`.
The index type of the commuting family is arbitrary.
-/

open _root_.Module
open scoped IsMulCommutative

variable {K V ι : Type*} [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def jointGenEigenspace (T : ι → Module.End K V) (χ : ι → K) : Submodule K V :=
  ⨅ i : ι, (T i).genEigenspace (χ i) ⊤

omit [IsAlgClosed K] [FiniteDimensional K V] in
theorem joint_independent (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    iSupIndep (fun χ : ι → K => jointGenEigenspace T χ) := by
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i).eq)

theorem joint_spans (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    (⨆ χ : ι → K, jointGenEigenspace T χ) = ⊤ := by
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    T (fun i j _ => hcomm i j) (fun i => (T i).iSup_maxGenEigenspace_eq_top)

omit [IsAlgClosed K] in
theorem joint_finite (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    Set.Finite {χ : ι → K | jointGenEigenspace T χ ≠ ⊥} :=
  Submodule.finite_ne_bot_of_iSupIndep (joint_independent T hcomm)

omit [IsAlgClosed K] [FiniteDimensional K V] in
theorem exists_polynomial_evaluation (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ ev : MvPolynomial ι K →ₐ[K] Module.End K V,
      ∀ i, ev (MvPolynomial.X i) = T i := by
  let A := Algebra.adjoin K (Set.range T)
  have : IsMulCommutative A := Algebra.isMulCommutative_adjoin K (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact fun _ => hcomm i j)
  let t : ι → A := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  exact ⟨A.val.comp (MvPolynomial.aeval t), fun i => by simp [t]⟩

theorem exists_common_eigenvector [Nontrivial V]
    (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  classical
  generalize hn : finrank K V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hall : ∀ i, ∃ μ : K, (T i).eigenspace μ = ⊤
    · choose χ hχ using hall
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine ⟨χ, v, hv, fun i => ?_⟩
      exact (Module.End.mem_eigenspace_iff.mp (hχ i ▸ Submodule.mem_top))
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      obtain ⟨μ, hμ⟩ := (T i).exists_eigenvalue
      let W := (T i).eigenspace μ
      have hW : W ≠ ⊥ := hμ
      have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      have hinv (j : ι) : Set.MapsTo (T j) W W :=
        Module.End.mapsTo_genEigenspace_of_comm (hcomm i j).eq μ 1
      let S : ι → Module.End K W := fun j => (T j).restrict (hinv j)
      have hS (j k : ι) : Commute (S j) (S k) := by
        ext v
        exact DFunLike.congr_fun (hcomm j k).eq (v : V)
      have hdim : finrank K W < n := hn ▸ Submodule.finrank_lt (hi μ)
      obtain ⟨χ, v, hv, he⟩ := ih (finrank K W) hdim S hS rfl
      refine ⟨χ, v, ?_, fun j => congrArg Subtype.val (he j)⟩
      intro hv0
      exact hv (Subtype.ext hv0)

omit [IsAlgClosed K] [FiniteDimensional K V] in
theorem joint_invariant (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) (χ : ι → K) (i : ι) :
    Set.MapsTo (T i) (jointGenEigenspace T χ) (jointGenEigenspace T χ) := by
  intro v hv
  change v ∈ ⨅ j, (T j).genEigenspace (χ j) ⊤ at hv
  change T i v ∈ ⨅ j, (T j).genEigenspace (χ j) ⊤
  simp only [Submodule.mem_iInf] at hv ⊢
  exact fun j => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) (χ j) (hv j)

theorem exists_joint_eigenvector (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) (χ : ι → K)
    (hχ : jointGenEigenspace T χ ≠ ⊥) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  let W := jointGenEigenspace T χ
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hχ
  let S : ι → Module.End K W := fun i => (T i).restrict (joint_invariant T hcomm χ i)
  have hS (i j : ι) : Commute (S i) (S j) := by
    ext v
    exact DFunLike.congr_fun (hcomm i j).eq (v : V)
  obtain ⟨η, v, hv, he⟩ := exists_common_eigenvector S hS
  have hv0 : (v : V) ≠ 0 := fun h => hv (Subtype.ext h)
  have hη (i : ι) : η i = χ i := by
    by_contra hne
    have hd := (T i).disjoint_genEigenspace hne 1 ⊤
    have hmem : (v : V) ∈ (T i).eigenspace (η i) ⊓ (T i).genEigenspace (χ i) ⊤ :=
      ⟨Module.End.mem_eigenspace_iff.mpr (congrArg Subtype.val (he i)),
        (Submodule.mem_iInf _).mp v.property i⟩
    rw [hd.eq_bot, Submodule.mem_bot] at hmem
    exact hv0 hmem
  exact ⟨v, hv0, fun i => hη i ▸ congrArg Subtype.val (he i)⟩

omit [IsAlgClosed K] [FiniteDimensional K V] in
theorem polynomial_on_eigenvector
    (ev : MvPolynomial ι K →ₐ[K] Module.End K V)
    (χ : ι → K) (v : V)
    (he : ∀ i, ev (MvPolynomial.X i) v = χ i • v)
    (p : MvPolynomial ι K) :
    ev p v = MvPolynomial.eval χ p • v := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq, add_smul]
  | mul_X p i hp =>
    simp [map_mul, Module.End.mul_apply, he, hp, smul_smul, mul_comm]

theorem polynomial_relation_on_joint_eigenvalues
    (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (ev : MvPolynomial ι K →ₐ[K] Module.End K V)
    (hev : ∀ i, ev (MvPolynomial.X i) = T i)
    (χ : ι → K) (p : MvPolynomial ι K)
    (hχ : jointGenEigenspace T χ ≠ ⊥) (hp : ev p = 0) :
    MvPolynomial.eval χ p = 0 := by
  obtain ⟨v, hv, he⟩ := exists_joint_eigenvector T hcomm χ hχ
  have h := polynomial_on_eigenvector ev χ v (fun i => hev i ▸ he i) p
  rw [hp, LinearMap.zero_apply] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hv

omit [IsAlgClosed K] [FiniteDimensional K V] in
theorem extending_basis_repr_castSucc {n : ℕ} {W : Submodule K V}
    (b : Basis (Fin n) K W) (B : Basis (Fin (n + 1)) K V)
    (hb : ∀ j, B j.castSucc = (b j : V)) (v : W) (r : Fin n) :
    B.repr (v : V) r.castSucc = b.repr v r := by
  classical
  have h : (B.coord r.castSucc).comp W.subtype = b.coord r := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, Basis.coord_apply, Submodule.subtype_apply, ← hb j,
      Basis.coord_apply]
    simp only [Basis.repr_self, Finsupp.single_apply, Fin.castSucc_inj]
  exact DFunLike.congr_fun h v

omit [IsAlgClosed K] [FiniteDimensional K V] in
theorem extending_basis_repr_last {n : ℕ} {W : Submodule K V}
    (b : Basis (Fin n) K W) (B : Basis (Fin (n + 1)) K V)
    (hb : ∀ j, B j.castSucc = (b j : V)) (v : W) :
    B.repr (v : V) (Fin.last n) = 0 := by
  classical
  have h : (B.coord (Fin.last n)).comp W.subtype = 0 := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, Basis.coord_apply, Submodule.subtype_apply, ← hb j]
    simp
  exact DFunLike.congr_fun h v

theorem exists_triangular_basis_aux (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (m : ℕ) (b : Basis (Fin m) K V),
      ∀ i (r c : Fin m), c < r → b.repr (T i (b c)) r = 0 := by
  classical
  generalize hn : finrank K V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    cases subsingleton_or_nontrivial V with
    | inl h =>
      exact ⟨0, Basis.empty V, fun _ r => Fin.elim0 r⟩
    | inr h =>
      let D : ι → Module.End K (Dual K V) := fun i => (T i).dualMap
      have hD (i j : ι) : Commute (D i) (D j) := by
        ext φ v
        exact congrArg φ (DFunLike.congr_fun (hcomm j i).eq v)
      obtain ⟨χ, φ, hφ, he⟩ := exists_common_eigenvector D hD
      obtain ⟨y, hy⟩ := LinearMap.surjective hφ (1 : K)
      let W := LinearMap.ker φ
      have hinv (i : ι) : Set.MapsTo (T i) W W := by
        intro v hv
        change φ (T i v) = 0
        have h := congrArg (fun ψ : Dual K V => ψ v) (he i)
        change φ (T i v) = χ i * φ v at h
        rw [h, show φ v = 0 from hv, mul_zero]
      let S : ι → Module.End K W := fun i => (T i).restrict (hinv i)
      have hS (i j : ι) : Commute (S i) (S j) := by
        ext v
        exact DFunLike.congr_fun (hcomm i j).eq (v : V)
      have hdim : finrank K W < n := by
        have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
        change finrank K W + 1 = finrank K V at hd
        omega
      obtain ⟨m, b, hb⟩ := ih (finrank K W) hdim S hS rfl
      have hli (a : K) (x : V) (hx : x ∈ W) (ha : a • y + x = 0) : a = 0 := by
        have h := congrArg φ ha
        simpa [map_add, map_smul, hy, show φ x = 0 from hx] using h
      have hsp (z : V) : ∃ a : K, z + a • y ∈ W := by
        refine ⟨-φ z, ?_⟩
        change φ (z + (-φ z) • y) = 0
        simp [hy]
      let B := b.mkFinSnoc y hli hsp
      have hB (j : Fin m) : B j.castSucc = (b j : V) := by
        simp [B, Basis.coe_mkFinSnoc]
      refine ⟨m + 1, B, ?_⟩
      intro i r c
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · refine Fin.lastCases ?_ (fun c' => ?_) c
        · intro hcr
          exact False.elim (lt_irrefl _ hcr)
        · intro _
          rw [hB]
          exact extending_basis_repr_last b B hB (S i (b c'))
      · refine Fin.lastCases ?_ (fun c' => ?_) c
        · intro hcr
          exact False.elim (not_lt_of_ge (Fin.le_last _) hcr)
        · intro hcr
          rw [hB]
          change B.repr ((S i (b c') : W) : V) r'.castSucc = 0
          rw [extending_basis_repr_castSucc b B hB (S i (b c')) r']
          exact hb i r' c' hcr

theorem exists_triangular_basis (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ i (r c : Fin (finrank K V)), c < r → b.repr (T i (b c)) r = 0 := by
  obtain ⟨m, b, hb⟩ := exists_triangular_basis_aux T hcomm
  have hm : finrank K V = m := by simpa using finrank_eq_card_basis b
  subst m
  exact ⟨b, hb⟩

/-- Commuting, with precisely the natural hypotheses and all conclusions of the specification. -/
theorem commuting_family_structure
    (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ ev : MvPolynomial ι K →ₐ[K] Module.End K V,
      (∀ i, ev (MvPolynomial.X i) = T i) ∧
      (∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
        ∀ i (r c : Fin (Module.finrank K V)),
          c < r → b.repr (T i (b c)) r = 0) ∧
      Set.Finite {χ : ι → K | jointGenEigenspace T χ ≠ ⊥} ∧
      iSupIndep (fun χ : ι → K => jointGenEigenspace T χ) ∧
      (⨆ χ : ι → K, jointGenEigenspace T χ) = ⊤ ∧
      (∀ (χ : ι → K) (p : MvPolynomial ι K),
        jointGenEigenspace T χ ≠ ⊥ →
        ev p = 0 → MvPolynomial.eval χ p = 0) := by
  obtain ⟨ev, hev⟩ := exists_polynomial_evaluation T hcomm
  exact ⟨ev, hev, exists_triangular_basis T hcomm, joint_finite T hcomm,
    joint_independent T hcomm, joint_spans T hcomm,
    fun χ p hχ hp => polynomial_relation_on_joint_eigenvalues T hcomm ev hev χ p hχ hp⟩

end OAI.LinearAlgebra.Endomorphisms.Commuting.Construction
