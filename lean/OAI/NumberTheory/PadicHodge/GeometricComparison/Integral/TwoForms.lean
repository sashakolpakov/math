import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import OAI.NumberTheory.PadicHodge.GeometricComparison.BilinearDiagonal

/-! # Two Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoForms.IntegralTwoForms

noncomputable section

/-! Native two-forms agree with exterior Kähler two-forms over arbitrary coefficient rings. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem update_pair (x y z : KaehlerDifferential R A) : Function.update ![x, y] 1 z = ![x, z] := by
  ext i
  fin_cases i <;> simp

def pairing : KaehlerDifferential R A →ₗ[A] KaehlerDifferential R A →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2 :=
  LinearMap.mk₂ A (fun x y => AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 2 ![x, y])
    (fun x y z => (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 2).cons_add ![z] x y)
    (fun a x y => (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 2).cons_smul ![y] a x)
    (fun x y z => by
      simpa only [update_pair] using
        (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 2).map_update_add ![x, y] 1 y z)
    (fun a x y => by
      simpa only [update_pair] using
        (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 2).map_update_smul ![x, y] 1 a y)

theorem pairing_D (a b : A) :
    pairing R A (KaehlerDifferential.D R A a) (KaehlerDifferential.D R A b) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 ![a, b] := by
  change AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 2
    ![KaehlerDifferential.D R A a, KaehlerDifferential.D R A b] = _
  convert AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols_D R A 2 ![a, b] using 1
  congr 1
  ext i
  fin_cases i <;> rfl

theorem pairing_skew (x y : KaehlerDifferential R A) :
    pairing R A x y + pairing R A y x = 0 := by
  have h : pairing R A + (pairing R A).flip = 0 := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
    intro a
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
    intro b
    change pairing R A (KaehlerDifferential.D R A a) (KaehlerDifferential.D R A b) +
      pairing R A (KaehlerDifferential.D R A b) (KaehlerDifferential.D R A a) = 0
    rw [pairing_D, pairing_D]
    simpa using (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbols R A 2).map_add_swap ![a, b] (i := 0) (j := 1) (by decide)
  exact congrArg (fun f : KaehlerDifferential R A →ₗ[A] KaehlerDifferential R A →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2 => f x y) h

theorem pairing_self (x : KaehlerDifferential R A) : pairing R A x x = 0 := by
  apply BilinearDiagonal.BilinearDiagonalSpan.diagonal_zero (pairing R A) (Set.range (KaehlerDifferential.D R A))
    (KaehlerDifferential.span_range_derivation R A) (pairing_skew R A)
  rintro _ ⟨a, rfl⟩
  rw [pairing_D]
  exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbols R A 2).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)

def alternating : AlternatingMap A (KaehlerDifferential R A) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2) (Fin 2) :=
  { AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 2 with
    map_eq_zero_of_eq' := by
      intro v i j hv hij
      have h01 : v 0 = v 1 := by
        fin_cases i <;> fin_cases j <;> simp_all
      have he : v = ![v 0, v 0] := by
        ext k
        fin_cases k <;> simp [h01]
      rw [he]
      exact pairing_self R A (v 0) }

def fromExterior : (⋀[A]^2 (KaehlerDifferential R A)) →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2 :=
  exteriorPower.alternatingMapLinearEquiv (alternating R A)

theorem fromExterior_symbol (v : Fin 2 → A) :
    fromExterior R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol R A 2 v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 v :=
  (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans
    (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols_D R A 2 v)

theorem left_inverse : Function.LeftInverse (fromExterior R A) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A 2) := by
  intro ω
  obtain ⟨f, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A 2).mkQ_surjective ω
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single v a =>
    change fromExterior R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A 2 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
    rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol, map_smul, fromExterior_symbol, ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

def equiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2 ≃ₗ[A] ⋀[A]^2 (KaehlerDifferential R A) :=
  LinearEquiv.ofBijective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A 2)
    ⟨(left_inverse R A).injective, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_surjective R A 2⟩

theorem equiv_symbol (a : A) (v : Fin 2 → A) :
    equiv R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol R A 2 v := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol R A a v

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoForms.IntegralTwoForms
