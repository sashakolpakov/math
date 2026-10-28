import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! # Factorization Spans -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FactorizationSpans

noncomputable section

/-! Finite sums of sections followed by morphisms compose. This keeps the
intermediate sheaf maps explicit and avoids choosing tensor reassociations. -/
open _root_.CategoryTheory _root_.CategoryTheory.Preadditive
open scoped BigOperators
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

def SectionFactorizationSpan (O M N : C) : Prop :=
  ∀ t : O ⟶ N, ∃ (n : ℕ) (s : Fin n → (O ⟶ M)) (a : Fin n → (M ⟶ N)),
    t = ∑ i, s i ≫ a i

namespace SectionFactorizationSpan
variable {O L M N : C}

theorem refl (O M : C) : SectionFactorizationSpan O M M := by
  intro t
  exact ⟨1, fun _ => t, fun _ => 𝟙 M, by simp⟩

theorem trans (h : SectionFactorizationSpan O L M) (k : SectionFactorizationSpan O M N) :
    SectionFactorizationSpan O L N := by
  classical
  intro t
  obtain ⟨n, s, a, ht⟩ := k t
  choose m v b hv using fun i => h (s i)
  let κ := Σ i : Fin n, Fin (m i)
  let e := Fintype.equivFin κ
  let w : κ → (O ⟶ L) := fun i => v i.1 i.2
  let c : κ → (L ⟶ N) := fun i => b i.1 i.2 ≫ a i.1
  refine ⟨Fintype.card κ, fun i => w (e.symm i), fun i => c (e.symm i), ?_⟩
  calc
    t = ∑ i, (∑ j, v i j ≫ b i j) ≫ a i := by rw [ht]; simp only [← hv]
    _ = ∑ i, ∑ j, v i j ≫ (b i j ≫ a i) := by simp only [sum_comp, Category.assoc]
    _ = ∑ i : κ, w i ≫ c i := by rw [Fintype.sum_sigma]
    _ = ∑ i, w (e.symm i) ≫ c (e.symm i) := (e.symm.sum_comp (fun i => w i ≫ c i)).symm

theorem sourceIso (h : SectionFactorizationSpan O L N) (e : L ≅ M) :
    SectionFactorizationSpan O M N := by
  intro t
  obtain ⟨n, s, a, ht⟩ := h t
  exact ⟨n, fun i => s i ≫ e.hom, fun i => e.inv ≫ a i,
    by simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ht⟩

theorem targetIso (h : SectionFactorizationSpan O L M) (e : M ≅ N) :
    SectionFactorizationSpan O L N := by
  intro t
  obtain ⟨n, s, a, ht⟩ := h (t ≫ e.inv)
  refine ⟨n, s, fun i => a i ≫ e.hom, ?_⟩
  have he := congrArg (fun f => f ≫ e.hom) ht
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, sum_comp] using he

end SectionFactorizationSpan

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FactorizationSpans
