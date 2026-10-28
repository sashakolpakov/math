import OAI.NumberTheory.PadicHodge.IntegralComparison.CentralNullHomotopy

/-! # Hom Acyclic -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclic

noncomputable section

/-! Exact Hom rows give actual cochain nullhomotopies by induction.
Scalar annihilation of the source and invertibility on coefficients
provide these rows without an injectivity hypothesis. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K : CochainComplex C ℕ) (M : C)

structure Rows : Prop where
  zero : ∀ (f : K.X 0 ⟶ M), ∃ g : K.X 1 ⟶ M, K.d 0 1 ≫ g = f
  succ : ∀ (n : ℕ) (f : K.X (n + 1) ⟶ M), K.d n (n + 1) ≫ f = 0 →
    ∃ g : K.X (n + 2) ⟶ M, K.d (n + 1) (n + 2) ≫ g = f

variable {K M}

theorem rows_of_scalar (R : Type w) [CommRing R] [Linear R C]
    (r : R) (h : Homotopy (r • 𝟙 K) 0) (b : M ⟶ M) (hb : r • b = 𝟙 M) : Rows K M := by
  constructor
  · intro f
    refine ⟨h.hom 1 0 ≫ f ≫ b, ?_⟩
    have hc := h.comm 0
    simp only [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
      HomologicalComplex.zero_f, add_zero] at hc
    change r • 𝟙 (K.X 0) = K.d 0 1 ≫ h.hom 1 0 at hc
    rw [← Category.assoc, ← Category.assoc, ← hc, Linear.smul_comp, Category.id_comp,
      Linear.smul_comp, ← Linear.comp_smul, hb, Category.comp_id]
  · intro n f hf
    refine ⟨h.hom (n + 2) (n + 1) ≫ f ≫ b, ?_⟩
    have hc := h.comm (n + 1)
    simp only [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
      HomologicalComplex.zero_f, add_zero] at hc
    have he := congrArg (fun z => z ≫ f ≫ b) hc
    change (r • 𝟙 (K.X (n + 1))) ≫ f ≫ b = _ at he
    simp only [add_comp, Category.assoc,
      Linear.smul_comp, Category.id_comp] at he
    have hfb : K.d n (n + 1) ≫ f ≫ b = 0 := by rw [← Category.assoc, hf, zero_comp]
    rw [hfb, comp_zero, add_zero] at he
    rw [← Linear.comp_smul, hb, Category.comp_id] at he
    exact he.symm

def null (L : CochainComplex C ℕ) (hL : ∀ n, Rows K (L.X n)) (f : K ⟶ L) : Homotopy f 0 := by
  let h₀ := ((hL 0).zero (f.f 0)).choose
  have hh₀ := ((hL 0).zero (f.f 0)).choose_spec
  have hz : K.d 0 1 ≫ (f.f 1 - h₀ ≫ L.d 0 1) = 0 := by
    rw [comp_sub, ← Category.assoc, hh₀, ← f.comm, sub_self]
  let h₁ := ((hL 1).succ 0 (f.f 1 - h₀ ≫ L.d 0 1) hz).choose
  have hh₁ := ((hL 1).succ 0 (f.f 1 - h₀ ≫ L.d 0 1) hz).choose_spec
  apply Homotopy.mkCoinductive f h₀ hh₀.symm h₁
    (by rw [hh₁]; abel)
  intro n p
  rcases p with ⟨a, b, hp⟩
  have hz : K.d (n + 1) (n + 2) ≫ (f.f (n + 2) - b ≫ L.d (n + 1) (n + 2)) = 0 := by
    rw [comp_sub, ← f.comm, hp, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add,
      Category.assoc, sub_self]
  let h₂ := ((hL (n + 2)).succ (n + 1) _ hz).choose
  have hh₂ := ((hL (n + 2)).succ (n + 1) _ hz).choose_spec
  exact ⟨h₂, by rw [hh₂]; abel⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclic
