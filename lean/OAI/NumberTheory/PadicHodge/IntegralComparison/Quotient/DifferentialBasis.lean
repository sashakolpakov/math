import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.BaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactDifferentialBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryBaseQuotient
import Mathlib.RingTheory.Flat.Basic

/-! # Differential Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DifferentialBasis

noncomputable section

/-! Exact coordinate bases for ordinary forms after quotienting the original coefficient base. -/

open scoped TensorProduct

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal R) (x : σ → A) (b : Module.Basis σ A (KaehlerDifferential R A))
  (hb : ∀ i, b i = KaehlerDifferential.D R A (x i))

local notation "S" => R ⧸ I
local notation "B" => A ⧸ I.map (algebraMap R A)

def kaehlerBasis : Module.Basis σ B (KaehlerDifferential S B) :=
  (b.baseChange B).map (BaseChange.differentials R A I)

include hb in
theorem kaehlerBasis_apply (i : σ) : kaehlerBasis R A σ I b i =
    KaehlerDifferential.D S B (Ideal.Quotient.mk (I.map (algebraMap R A)) (x i)) := by
  rw [kaehlerBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, hb]
  simpa only [map_one, one_smul] using BaseChange.differentials_tmul_D R A I 1 (x i)

variable [LinearOrder σ]

def quotientBasis (n : ℕ) : Module.Basis (Set.powersetCard σ n) B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B n) :=
  ExactDifferentialBasis.basis S B σ
    (fun i => Ideal.Quotient.mk (I.map (algebraMap R A)) (x i)) n (kaehlerBasis R A σ I b)
      (kaehlerBasis_apply R A σ I x b hb)

def basis (n : ℕ) : Module.Basis (Set.powersetCard σ n) B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :=
  (quotientBasis R A σ I x b hb n).map
    (OrdinaryBaseQuotient.Ordinary.formsEquiv R S B Ideal.Quotient.mk_surjective n).symm

theorem basis_apply (n : ℕ) (s : Set.powersetCard σ n) : basis R A σ I x b hb n s =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B 1
      (fun j => Ideal.Quotient.mk (I.map (algebraMap R A)) (x (Set.powersetCard.ofFinEmbEquiv.symm s j))) := by
  rw [basis, Module.Basis.map_apply, quotientBasis, ExactDifferentialBasis.basis_apply]
  apply (OrdinaryBaseQuotient.Ordinary.formsEquiv R S B Ideal.Quotient.mk_surjective n).injective
  rw [LinearEquiv.apply_symm_apply, OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol]
  rfl

include x b hb in
theorem finite [Finite σ] (n : ℕ) : Module.Finite B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :=
  Module.Finite.of_basis (basis R A σ I x b hb n)

include x b hb in
theorem free (n : ℕ) : Module.Free B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :=
  Module.Free.of_basis (basis R A σ I x b hb n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DifferentialBasis
