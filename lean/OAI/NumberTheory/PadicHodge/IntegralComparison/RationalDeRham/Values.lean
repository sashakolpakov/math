import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Wedge

/-! # Values -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Values.Wedge

noncomputable section

/-! Canonical values of the actual differential symbols in the
exterior algebra, retaining both wedge products and differentiation. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

def word (n : ℕ) (v : Fin n → A) : ExteriorAlgebra A Ω[A⁄R] :=
  ExteriorAlgebra.ιMulti A n (fun i => KaehlerDifferential.D R A (v i))

def value (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[A] ExteriorAlgebra A Ω[A⁄R] :=
  (Submodule.subtype (⋀[A]^n Ω[A⁄R])).comp (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A n).toLinearMap

theorem value_injective (n : ℕ) : Function.Injective (value R A n) :=
  Subtype.val_injective.comp (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A n).injective

theorem value_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    value R A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a • word R A n v := by
  change (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) : ExteriorAlgebra A Ω[A⁄R]) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv_symbol]
  rfl

omit [Algebra ℚ A] in
theorem word_append (p q : ℕ) (v : Fin p → A) (w : Fin q → A) :
    word R A (p + q) (Fin.append v w) = word R A p v * word R A q w := by
  unfold word
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

omit [Algebra ℚ A] in
theorem word_cons (n : ℕ) (a : A) (v : Fin n → A) :
    word R A (n + 1) (Fin.cons a v) =
      ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) * word R A n v := by
  simp only [word, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, Matrix.vecTail,
    Function.comp_def, Fin.cons_succ]

theorem value_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    value R A (p + q) (Wedge.wedge R A p q x y) = value R A p x * value R A q y :=
  Wedge.toExterior_wedge_coe R A p q x y

theorem value_degreeCast {m n : ℕ} (h : m = n) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m) :
    value R A n (Wedge.degreeCast R A h x) = value R A m x := by
  subst n
  rfl

def differentialValue (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[R] ExteriorAlgebra A Ω[A⁄R] :=
  ((value R A (n + 1)).restrictScalars R).comp (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n)

theorem differentialValue_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    differentialValue R A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) * word R A n v := by
  change value R A (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol, value_symbol, one_smul, word_cons]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Values.Wedge
