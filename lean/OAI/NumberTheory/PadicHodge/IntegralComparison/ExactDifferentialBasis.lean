import OAI.NumberTheory.PadicHodge.IntegralComparison.AlternatingOrderedSpan
import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Exact Differential Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactDifferentialBasis

noncomputable section

/-!
# IntegralComparison: bases of ordinary differential symbols in arbitrary characteristic

An exact Kähler basis gives a basis of every differential-symbol module.
Spanning follows from tensor symbols and ordering alternating tuples;
independence follows from the native exterior-power basis.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [LinearOrder σ] (x : σ → A) (n : ℕ)

def coordinateForm (s : Set.powersetCard σ n) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (fun j => x (Set.powersetCard.ofFinEmbEquiv.symm s j))

theorem toExterior_coordinateForm (s : Set.powersetCard σ n) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A n (coordinateForm R A σ x n s) =
      exteriorPower.ιMulti_family A n (fun i => KaehlerDifferential.D R A (x i)) s := by
  rw [coordinateForm, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol, one_smul]
  rfl

theorem span_eq_top (hx : Submodule.span A (Set.range (fun i => KaehlerDifferential.D R A (x i))) = ⊤) :
    Submodule.span A (Set.range (coordinateForm R A σ x n)) = ⊤ := by
  let S := Submodule.span A (Set.range (coordinateForm R A σ x n))
  have ht := PiTensorProduct.submodule_span_eq_top
    (g := fun {_ : Fin n} (i : σ) => KaehlerDifferential.D R A (x i)) (fun _ => hx)
  have hle : (⊤ : Submodule A (PiTensorProduct A (fun _ : Fin n => KaehlerDifferential R A))) ≤
      S.comap (DifferentialFormFiniteness.tensorSymbols R A n) := by
    rw [← ht]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change DifferentialFormFiniteness.tensorSymbols R A n
      (PiTensorProduct.tprod A (fun i => KaehlerDifferential.D R A (x (v i)))) ∈ S
    rw [DifferentialFormFiniteness.tensorSymbols_tprod]
    exact AlternatingOrderedSpan.mem_span R A A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) σ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbols R A n) x v
  apply top_unique
  intro ω _
  obtain ⟨t, rfl⟩ := DifferentialFormFiniteness.tensorSymbols_surjective R A n ω
  exact hle (Submodule.mem_top)

variable (b : Module.Basis σ A (KaehlerDifferential R A))
  (hx : ∀ i, b i = KaehlerDifferential.D R A (x i))

include hx in
theorem linearIndependent : LinearIndependent A (coordinateForm R A σ x n) := by
  apply LinearIndependent.of_comp (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A n)
  have he : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A n) ∘ coordinateForm R A σ x n = exteriorPower.ιMulti_family A n b := by
    funext s
    rw [Function.comp_apply, toExterior_coordinateForm]
    exact congrArg (fun v => exteriorPower.ιMulti_family A n v s) (funext (fun i => (hx i).symm))
  rw [he]
  exact exteriorPower.ιMulti_family_linearIndependent_ofBasis A n b

def basis : Module.Basis (Set.powersetCard σ n) A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  Module.Basis.mk (linearIndependent R A σ x n b hx)
    (eq_top_iff.mp (span_eq_top R A σ x n ((congrArg (fun v => Submodule.span A (Set.range v))
      (funext hx)).symm.trans b.span_eq)))

theorem basis_apply (s : Set.powersetCard σ n) : basis R A σ x n b hx s = coordinateForm R A σ x n s :=
  Module.Basis.mk_apply _ _ _

def exteriorEquiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[A] ⋀[A]^n (KaehlerDifferential R A) :=
  (basis R A σ x n b hx).equiv (b.exteriorPower n) (Equiv.refl _)

theorem exteriorEquiv_eq : (exteriorEquiv R A σ x n b hx).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A n := by
  apply (basis R A σ x n b hx).ext
  intro s
  change (basis R A σ x n b hx).equiv (b.exteriorPower n) (Equiv.refl _) (basis R A σ x n b hx s) = _
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, exteriorPower.basis_apply, ExactDifferentialBasis.basis_apply,
    toExterior_coordinateForm]
  exact congrArg (fun v => exteriorPower.ιMulti_family A n v s) (funext hx)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactDifferentialBasis
