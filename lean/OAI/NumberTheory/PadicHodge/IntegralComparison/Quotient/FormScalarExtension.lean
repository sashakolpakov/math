import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DifferentialBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ModuleFlatness
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.BasisBaseChange
import Mathlib.RingTheory.Flat.Stability

/-! # Form Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormScalarExtension

noncomputable section

/-! The actual form pullback realizes quotient scalar extension and has flat coefficient modules. -/

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [LinearOrder σ]
  (I : Ideal R) (x : σ → A) (b : Module.Basis σ A (KaehlerDifferential R A))
  (hb : ∀ i, b i = KaehlerDifferential.D R A (x i))

local notation "S" => R ⧸ I
local notation "B" => A ⧸ I.map (algebraMap R A)

theorem map_basis (n : ℕ) (s : Set.powersetCard σ n) :
    OrdinaryFormScalars.Ordinary.map R A B n (ExactDifferentialBasis.basis R A σ x n b hb s) =
      DifferentialBasis.basis R A σ I x b hb n s := by
  rw [ExactDifferentialBasis.basis_apply, ExactDifferentialBasis.coordinateForm,
    OrdinaryFormScalars.Ordinary.map_symbol, DifferentialBasis.basis_apply, map_one]
  rfl

include σ x b hb in
theorem isBaseChange (n : ℕ) : IsBaseChange B (OrdinaryFormScalars.Ordinary.map R A B n) :=
  BasisBaseChange.isBaseChange (OrdinaryFormScalars.Ordinary.map R A B n)
    (ExactDifferentialBasis.basis R A σ x n b hb)
    (DifferentialBasis.basis R A σ I x b hb n)
    (map_basis R A σ I x b hb n)

include σ x b hb in
theorem flat [Module.Flat R A] (n : ℕ) : Module.Flat S (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) := by
  let : Module.Flat S B := ModuleFlatness.flat R A I
  let : Module.Free B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) := DifferentialBasis.free R A σ I x b hb n
  exact Module.Flat.trans S B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormScalarExtension
