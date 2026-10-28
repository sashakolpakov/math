import OAI.AlgebraicTopology.Cohomology.Singular.Formulas

/-! # Simplicial Cochain Of Values -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SimplicialCochainOfValues

noncomputable section

/-!
# Cochain maps specified by actual simplex values

The existing simplicial cochain objects are canonically all functions on
simplices. A degreewise linear family of such functions defines a cochain
map exactly when it satisfies the alternating-face formula. This file
packages that elementary implication and its naturality; analytic Stokes
identities remain explicit premises until supplied by actual integration.
-/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.Formulas

variable {R : Type} [Ring R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
  (S : SSet.{0}) (A : ModuleCat.{0} R)
  (I : ∀ n : ℕ, C.X n →ₗ[R] (S _⦋n⦌ → A))

/-- Convert an actual function-valued linear map to the existing simplicial
cochain object, using its proved degreewise function isomorphism. -/
def simplicialCochainOfValues (n : ℕ) : C.X n ⟶ (Cohomology.Singular.Basic.simplicialCochains S A).X n :=
  ModuleCat.ofHom (I n) ≫ (Cohomology.Singular.Coefficients.degreewiseFunctionIso S A n).inv

@[simp]
theorem simplicialCochainOfValues_function (n : ℕ) (x : C.X n) :
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso S A n).hom (simplicialCochainOfValues C S A I n x) =
      I n x :=
  Iso.inv_hom_id_apply (Cohomology.Singular.Coefficients.degreewiseFunctionIso S A n) (I n x)

/-- An actual alternating-face identity is precisely the condition needed
to package the specified simplex values as a cochain map. -/
def simplicialCochainMapOfValues
    (hI : ∀ (n : ℕ) (x : C.X n) (s : S _⦋n + 1⦌),
      I (n + 1) (C.d n (n + 1) x) s =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • I n x (S.δ i s)) :
    C ⟶ Cohomology.Singular.Basic.simplicialCochains S A :=
  CochainComplex.ofHom (simplicialCochainOfValues C S A I) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Cohomology.Singular.Coefficients.degreewiseFunctionIso S A (n + 1)).toLinearEquiv.injective
    funext s
    change (Cohomology.Singular.Coefficients.degreewiseFunctionIso S A (n + 1)).hom
        ((Cohomology.Singular.Basic.simplicialCochains S A).d n (n + 1)
          (simplicialCochainOfValues C S A I n x)) s =
      (Cohomology.Singular.Coefficients.degreewiseFunctionIso S A (n + 1)).hom
        (simplicialCochainOfValues C S A I (n + 1) (C.d n (n + 1) x)) s
    rw [Cohomology.Singular.Formulas.degreewiseFunctionIso_coboundary]
    change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      ((Cohomology.Singular.Coefficients.degreewiseFunctionIso S A n).hom
        ((Cohomology.Singular.Coefficients.degreewiseFunctionIso S A n).inv (I n x))) (S.δ i s)) =
      ((Cohomology.Singular.Coefficients.degreewiseFunctionIso S A (n + 1)).hom
        ((Cohomology.Singular.Coefficients.degreewiseFunctionIso S A (n + 1)).inv
          (I (n + 1) (C.d n (n + 1) x)))) s
    simp only [Iso.inv_hom_id_apply]
    exact (hI n x s).symm)

variable (hI : ∀ (n : ℕ) (x : C.X n) (s : S _⦋n + 1⦌),
  I (n + 1) (C.d n (n + 1) x) s =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • I n x (S.δ i s))

@[simp]
theorem simplicialCochainMapOfValues_f (n : ℕ) :
    (simplicialCochainMapOfValues C S A I hI).f n =
      simplicialCochainOfValues C S A I n := rfl

@[simp]
theorem simplicialCochainMapOfValues_function (n : ℕ) (x : C.X n) :
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso S A n).hom
      ((simplicialCochainMapOfValues C S A I hI).f n x) = I n x :=
  simplicialCochainOfValues_function C S A I n x

/-- Evaluation of the packaged cochain gives exactly the prescribed actual
simplex value. -/
@[simp]
theorem simplicialCochainMapOfValues_evaluation (n : ℕ) (x : C.X n)
    (s : S _⦋n⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation S A s ((simplicialCochainMapOfValues C S A I hI).f n x) =
      I n x s := by
  rw [← Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, simplicialCochainMapOfValues_function]

variable {C S A I}
variable {D : CochainComplex (ModuleCat.{0} R) ℕ} {T : SSet.{0}}
  (J : ∀ n : ℕ, D.X n →ₗ[R] (T _⦋n⦌ → A))
  (hJ : ∀ (n : ℕ) (x : D.X n) (s : T _⦋n + 1⦌),
    J (n + 1) (D.d n (n + 1) x) s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • J n x (T.δ i s))

/-- Compatibility of the actual simplex values implies naturality of the
packaged cochain maps under a source cochain map and simplicial pullback. -/
theorem simplicialCochainMapOfValues_naturality
    (α : C ⟶ D) (f : T ⟶ S)
    (hnat : ∀ (n : ℕ) (x : C.X n) (s : T _⦋n⦌),
      J n (α.f n x) s = I n x (f.app _ s)) :
    α ≫ simplicialCochainMapOfValues D T A J hJ =
      simplicialCochainMapOfValues C S A I hI ≫ Cohomology.Singular.Functor.simplicialPullback A f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (Cohomology.Singular.Coefficients.degreewiseFunctionIso T A n).toLinearEquiv.injective
  funext s
  change (Cohomology.Singular.Coefficients.degreewiseFunctionIso T A n).hom
      ((simplicialCochainMapOfValues D T A J hJ).f n (α.f n x)) s =
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso T A n).hom
      ((Cohomology.Singular.Functor.simplicialPullback A f).f n
        ((simplicialCochainMapOfValues C S A I hI).f n x)) s
  rw [simplicialCochainMapOfValues_function, Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback,
    simplicialCochainMapOfValues_function]
  exact hnat n x s

end

end OAI.AlgebraicTopology.DeRham.Comparison.SimplicialCochainOfValues
