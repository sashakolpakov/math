import Mathlib

/-! # Hermitian Diagonal -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianDiagonal.Construction

noncomputable section

/-! Orthogonal bases for Hermitian forms with a nontrivial field involution.
The proof works directly with semilinear forms, including indefinite forms. -/

open _root_.Module LinearMap

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
variable (σ : E →+* E) (B : V →ₛₗ[σ] V →ₗ[E] E)

theorem semilinear_self_ne_zero (hne : ∃ a : E, σ a ≠ a) (hB : B ≠ 0) :
    ∃ x, B x x ≠ 0 := by
  by_contra! hz
  apply hB
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨a, ha⟩ := hne
  have hxy : B x y + B y x = 0 := by
    have hh := hz (x + y)
    simpa only [map_add, LinearMap.add_apply, hz, zero_add, add_zero, add_comm] using hh
  have haxy : a * B x y + σ a * B y x = 0 := by
    have hh := hz (x + a • y)
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
      RingHom.id_apply, smul_eq_mul, hz, mul_zero, zero_add, add_zero] at hh
    simpa only [add_comm] using hh
  change B x y = 0
  have hmul : (a - σ a) * B x y = 0 := by linear_combination haxy - σ a * hxy
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ha.symm)

theorem semilinear_orthogonal_singleton_ker (x : V) :
    (E ∙ x).orthogonalBilin B = LinearMap.ker (B x) := by
  ext y
  simp only [Submodule.mem_orthogonalBilin, LinearMap.mem_ker]
  constructor
  · exact fun h => h x (Submodule.mem_span_singleton_self x)
  · intro h z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smulₛₗ₂, h, smul_zero]

theorem semilinear_orthogonal_isCompl (x : V) (hx : B x x ≠ 0) :
    IsCompl (E ∙ x) ((E ∙ x).orthogonalBilin B) where
  disjoint := disjoint_iff.mpr (LinearMap.span_singleton_inf_orthogonal_eq_bot B x hx)
  codisjoint := by
    rw [codisjoint_iff, semilinear_orthogonal_singleton_ker]
    exact (B x).span_singleton_sup_ker_eq_top hx

theorem hermitian_orthogonal_basis [FiniteDimensional E V]
    (hne : ∃ a : E, σ a ≠ a) (hsym : B.IsSymm) :
    ∃ b : Basis (Fin (Module.finrank E V)) E V, B.IsOrthoᵢ b := by
  suffices ∀ d, Module.finrank E V = d → ∃ b : Basis (Fin d) E V, B.IsOrthoᵢ b by exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  | succ d ih =>
    obtain rfl | hB := eq_or_ne B 0
    · let b := Module.finBasis E V
      rw [hd] at b
      exact ⟨b, fun _ _ _ => rfl⟩
    obtain ⟨x, hx⟩ := semilinear_self_ne_zero σ B hne hB
    rw [← Submodule.finrank_add_eq_of_isCompl (semilinear_orthogonal_isCompl σ B x hx).symm,
      finrank_span_singleton (ne_zero_of_map hx)] at hd
    let W := (E ∙ x).orthogonalBilin B
    let B' := B.domRestrict₁₂ W W
    obtain ⟨b', hb'⟩ := ih B' (hsym.domRestrict W) (Nat.succ.inj hd)
    let b := Basis.mkFinCons x b'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have hdis := (semilinear_orthogonal_isCompl σ B x hx).disjoint
        rw [Submodule.disjoint_def] at hdis
        have hz := hdis (c • x) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) hy
        exact (smul_eq_zero.mp hz).resolve_right (fun hz => hx (hz.symm ▸ map_zero _)))
      (by
        intro y
        refine ⟨-B x y / B x x, fun z hz => ?_⟩
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
        simp only [map_smulₛₗ₂, map_add, map_smul, smul_eq_mul]
        field_simp
        ring)
    refine ⟨b, ?_⟩
    rw [Basis.coe_mkFinCons]
    intro j i
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    · exact (hij rfl).elim
    · rw [← hsym.eq x (b' j), (b' j).property x (Submodule.mem_span_singleton_self x), map_zero]
    · exact (b' i).property x (Submodule.mem_span_singleton_self x)
    · exact hb' (ne_of_apply_ne _ hij)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianDiagonal.Construction
