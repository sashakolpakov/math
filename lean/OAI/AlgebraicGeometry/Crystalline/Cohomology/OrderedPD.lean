import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PDForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsExterior
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Ordered PD -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrderedPD.OrderedPDSymbols

noncomputable section

/-!
# Ordered coordinate symbols for divided-power forms

Alternation puts every coordinate symbol in the span of symbols with
strictly increasing coordinate indices.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def symbols (n : ℕ) : AlternatingMap R A (PD.DeRham.PDDeRham.Form R A I δ n) (Fin n) :=
  ((PD.DeRham.PDDeRham.relations R A I δ n).mkQ.restrictScalars R).compAlternatingMap
    (DeRhamPresentationTo.DeRhamPresentation.symbols R A n)

theorem symbols_apply (n : ℕ) (v : Fin n → A) :
    symbols R A I δ n v = PD.DeRham.PDDeRham.symbol R A I δ 1 v := rfl

variable {σ : Type u} [LinearOrder σ] (x : σ → A)

def ordered (n : ℕ) (s : Set.powersetCard σ n) : PD.DeRham.PDDeRham.Form R A I δ n :=
  PD.DeRham.PDDeRham.symbol R A I δ 1 (x ∘ Set.powersetCard.ofFinEmbEquiv.symm s)

theorem symbol_mem_orderedSpan (n : ℕ) (t : Fin n → σ) :
    PD.DeRham.PDDeRham.symbol R A I δ 1 (x ∘ t) ∈ Submodule.span A (Set.range (ordered R A I δ x n)) := by
  classical
  change symbols R A I δ n (x ∘ t) ∈ _
  by_cases ht : Function.Injective t
  · suffices ∃ e : Equiv.Perm (Fin n), symbols R A I δ n ((x ∘ t) ∘ e) ∈
        Submodule.span A (Set.range (ordered R A I δ x n)) by
      obtain ⟨e, he⟩ := this
      rw [(symbols R A I δ n).map_congr_perm (x ∘ t) e]
      exact Submodule.smul_of_tower_mem _ _ he
    have hc : (Finset.image t Finset.univ).card = n :=
      (Finset.card_image_of_injective Finset.univ ht).trans (Finset.card_fin n)
    use (Finset.orderIsoOfFin (Finset.image t Finset.univ) hc).toEquiv.trans
      ((Set.equivOfEq Fintype.coe_image_univ).trans (Equiv.ofInjective t ht).symm)
    apply Submodule.subset_span
    refine ⟨⟨Finset.image t Finset.univ, hc⟩, ?_⟩
    change PD.DeRham.PDDeRham.symbol R A I δ 1 _ = PD.DeRham.PDDeRham.symbol R A I δ 1 _
    congr 1
    ext i
    simp [Equiv.apply_ofInjective_symm]
    rfl
  · have hz := (symbols R A I δ n).map_eq_zero_of_not_injective (x ∘ t)
      (fun h => ht (Function.Injective.of_comp h))
    rw [hz]
    exact Submodule.zero_mem _

theorem span_ordered_eq_top
    (hspan : Submodule.span A (Set.range (fun i => PD.OneForms.PDOneForms.D R A I δ (x i))) = ⊤) (n : ℕ) :
    Submodule.span A (Set.range (ordered R A I δ x n)) = ⊤ := by
  apply top_unique
  rw [← Finite.PDForms.FinitePDForms.coordinateSpan_eq_top R A I δ x hspan n]
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact symbol_mem_orderedSpan R A I δ x n t

variable (b : Module.Basis σ A (PD.DeRham.PDDeRham.Form R A I δ 1))
  (hb : ∀ i, b i = PD.OneForms.PDOneForms.D R A I δ (x i))

include hb in
theorem toExterior_ordered (n : ℕ) (s : Set.powersetCard σ n) :
    PD.FormsExterior.PDFormsExterior.toExterior R A I δ n (ordered R A I δ x n s) = b.exteriorPower n s := by
  rw [ordered, PD.FormsExterior.PDFormsExterior.toExterior_symbol, one_smul, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family]
  unfold PD.FormsExterior.PDFormsExterior.exteriorSymbol
  congr 1
  funext i
  exact (hb _).symm

include hb in
theorem ordered_linearIndependent (n : ℕ) : LinearIndependent A (ordered R A I δ x n) := by
  apply LinearIndependent.of_comp (PD.FormsExterior.PDFormsExterior.toExterior R A I δ n)
  have he : (PD.FormsExterior.PDFormsExterior.toExterior R A I δ n) ∘ (ordered R A I δ x n) = b.exteriorPower n :=
    funext (fun s => toExterior_ordered R A I δ x b hb n s)
  rw [he]
  exact (b.exteriorPower n).linearIndependent

omit [LinearOrder σ] in
include hb in
theorem coordinate_span : Submodule.span A (Set.range (fun i => PD.OneForms.PDOneForms.D R A I δ (x i))) = ⊤ := by
  have he : (fun i => PD.OneForms.PDOneForms.D R A I δ (x i)) = b := funext (fun i => (hb i).symm)
  rw [he]
  exact b.span_eq

/-- Increasing coordinate symbols form a basis whenever their one-forms form a basis. -/
def basis (n : ℕ) : Module.Basis (Set.powersetCard σ n) A (PD.DeRham.PDDeRham.Form R A I δ n) :=
  Module.Basis.mk (ordered_linearIndependent R A I δ x b hb n)
    (eq_top_iff.mp (span_ordered_eq_top R A I δ x (coordinate_span R A I δ x b hb) n))

theorem basis_apply (n : ℕ) (s : Set.powersetCard σ n) :
    basis R A I δ x b hb n s = ordered R A I δ x n s := Module.Basis.mk_apply _ _ _

include hb in
theorem toExterior_injective (n : ℕ) : Function.Injective (PD.FormsExterior.PDFormsExterior.toExterior R A I δ n) := by
  let c := basis R A I δ x b hb n
  have he : c.constr A (b.exteriorPower n) = PD.FormsExterior.PDFormsExterior.toExterior R A I δ n := by
    apply c.ext
    intro s
    rw [Module.Basis.constr_basis]
    exact (toExterior_ordered R A I δ x b hb n s).symm.trans
      (congrArg (PD.FormsExterior.PDFormsExterior.toExterior R A I δ n) (OrderedPDSymbols.basis_apply R A I δ x b hb n s).symm)
  rw [← he]
  exact c.injective_constr_of_linearIndependent (b.exteriorPower n).linearIndependent

/-- When coordinate differentials form a basis, higher PD forms are their exterior powers. -/
def formsEquiv (n : ℕ) : PD.DeRham.PDDeRham.Form R A I δ n ≃ₗ[A] ⋀[A]^n (PD.DeRham.PDDeRham.Form R A I δ 1) :=
  LinearEquiv.ofBijective (PD.FormsExterior.PDFormsExterior.toExterior R A I δ n)
    ⟨toExterior_injective R A I δ x b hb n, PD.FormsExterior.PDFormsExterior.toExterior_surjective R A I δ n⟩

theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R A I δ x b hb n (PD.DeRham.PDDeRham.symbol R A I δ a v) =
      a • PD.FormsExterior.PDFormsExterior.exteriorSymbol R A I δ n v :=
  PD.FormsExterior.PDFormsExterior.toExterior_symbol R A I δ a v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrderedPD.OrderedPDSymbols
