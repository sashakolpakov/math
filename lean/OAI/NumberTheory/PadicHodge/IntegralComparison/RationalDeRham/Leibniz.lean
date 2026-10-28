import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Values
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.WordSign

/-! # Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Leibniz.Wedge

noncomputable section

/-! The original de Rham differential obeys the graded Leibniz rule
for the canonically normalized wedge product. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

omit [Algebra ℚ A] in
theorem linearMap_ext_symbols {M : Type*} [AddCommGroup M] [Module R M]
    (n : ℕ) {f g : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[R] M}
    (h : ∀ (a : A) (v : Fin n → A), f (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = g (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) x
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a => exact h a v

theorem differentialValue_wedge_symbols (p q : ℕ) (a b : A)
    (v : Fin p → A) (w : Fin q → A) :
    Values.Wedge.differentialValue R A (p + q) (Wedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) =
      Values.Wedge.differentialValue R A p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) * Values.Wedge.value R A q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w) +
        (-1 : ℤ) ^ p • (Values.Wedge.value R A p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) * Values.Wedge.differentialValue R A q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) := by
  rw [Wedge.wedge_symbol, Values.Wedge.differentialValue_symbol, Values.Wedge.word_append,
    Values.Wedge.differentialValue_symbol, Values.Wedge.differentialValue_symbol, Values.Wedge.value_symbol, Values.Wedge.value_symbol]
  have hs : ExteriorAlgebra.ι A (KaehlerDifferential.D R A b) * Values.Wedge.word R A p v =
      (-1 : ℤ) ^ p • (Values.Wedge.word R A p v * ExteriorAlgebra.ι A (KaehlerDifferential.D R A b)) :=
    Exterior.WordSign.generator_word (KaehlerDifferential.D R A b) p
      (fun i => KaehlerDifferential.D R A (v i))
  calc
    _ = a • ((ExteriorAlgebra.ι A (KaehlerDifferential.D R A b) * Values.Wedge.word R A p v) * Values.Wedge.word R A q w) +
        b • ((ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) * Values.Wedge.word R A p v) * Values.Wedge.word R A q w) := by
      simp only [Derivation.leibniz, map_add, map_smul, add_mul, smul_mul_assoc, mul_assoc]
    _ = a • ((-1 : ℤ) ^ p •
          ((Values.Wedge.word R A p v * ExteriorAlgebra.ι A (KaehlerDifferential.D R A b)) * Values.Wedge.word R A q w)) +
        b • ((ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) * Values.Wedge.word R A p v) * Values.Wedge.word R A q w) := by
      rw [hs, smul_mul_assoc]
    _ = _ := by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc, smul_comm a ((-1 : ℤ) ^ p)]
      exact add_comm _ _

theorem differentialValue_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    Values.Wedge.differentialValue R A (p + q) (Wedge.wedge R A p q x y) =
      Values.Wedge.differentialValue R A p x * Values.Wedge.value R A q y +
        (-1 : ℤ) ^ p • (Values.Wedge.value R A p x * Values.Wedge.differentialValue R A q y) := by
  let L : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] ExteriorAlgebra A Ω[A⁄R] :=
    ((Wedge.wedge R A p q).restrictScalars₁₂ R R).compr₂ (Values.Wedge.differentialValue R A (p + q))
  let μ := LinearMap.mul R (ExteriorAlgebra A Ω[A⁄R])
  let D : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] ExteriorAlgebra A Ω[A⁄R] :=
    μ.compl₁₂ (Values.Wedge.differentialValue R A p) ((Values.Wedge.value R A q).restrictScalars R) +
      (-1 : ℤ) ^ p • μ.compl₁₂ ((Values.Wedge.value R A p).restrictScalars R) (Values.Wedge.differentialValue R A q)
  have h : L = D := by
    apply linearMap_ext_symbols R A p
    intro a v
    apply linearMap_ext_symbols R A q
    intro b w
    exact differentialValue_wedge_symbols R A p q a b v w
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

theorem differential_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A (p + q) (Wedge.wedge R A p q x y) =
      Wedge.degreeCast R A (by omega : (p + 1) + q = p + q + 1)
        (Wedge.wedge R A (p + 1) q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A p x) y) +
      (-1 : ℤ) ^ p • Wedge.degreeCast R A (by omega : p + (q + 1) = p + q + 1)
        (Wedge.wedge R A p (q + 1) x (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A q y)) := by
  apply Values.Wedge.value_injective R A (p + q + 1)
  rw [map_add, map_zsmul, Values.Wedge.value_degreeCast, Values.Wedge.value_degreeCast, Values.Wedge.value_wedge, Values.Wedge.value_wedge]
  exact differentialValue_wedge R A p q x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Leibniz.Wedge
