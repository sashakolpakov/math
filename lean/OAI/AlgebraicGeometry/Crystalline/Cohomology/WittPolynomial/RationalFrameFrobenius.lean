import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobeniusCompatibility
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyBijective

/-! # Rational Frame Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius

noncomputable section

/-! # The actual semilinear polynomial frame Frobenius is a rational quasi-isomorphism -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k B Tower
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "ψ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius.scalarEquiv p k
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.complexMap p k σ
local notation "O" => OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius.complex p k σ
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius.frobenius p k σ

abbrev complex : CochainComplex (ModuleCat.{u} K₀) ℕ :=
  ((IntrinsicScalarExtension.functor W K₀).mapHomologicalComplex (.up ℕ)).obj C

omit [Fintype σ] [LinearOrder σ] in
theorem scalar_base (w : W) : (ψ).toRingHom (algebraMap W K₀ w) = algebraMap W K₀ ((φ).toRingHom w) :=
  RationalPolynomial.RationalPolynomialCoefficientFrobenius.scalarEquiv_base p k w

def formMap (n : ℕ) : (K₀ ⊗[W] (C).X n) →ₛₗ[(ψ).toRingHom] (K₀ ⊗[W] (C).X n) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange (φ).toRingHom (ψ).toRingHom (scalar_base p k) ((G).f n)

def complexMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (ψ).toRingHom (complex p k σ) (complex p k σ) where
  f n := formMap p k σ n
  comm i j x := by
    change formMap p k σ j (((C).d i j).hom.baseChange K₀ x) =
      ((C).d i j).hom.baseChange K₀ (formMap p k σ i x)
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a ω =>
      exact congrArg (fun z : (C).X j => (ψ).toRingHom a ⊗ₜ[W] z) ((G).comm i j ω)

def comparisonIso : O ≅ complex p k σ :=
  ((IntrinsicScalarExtension.functor W K₀).mapHomologicalComplex (.up ℕ)).mapIso
    (PolynomialComplex.WittPolynomialComplex.complexIso p k σ)

theorem intertwines (n : ℕ) (x : (O).X n) :
    (comparisonIso p k σ).hom.f n ((F).f n x) =
      (complexMap p k σ).f n ((comparisonIso p k σ).hom.f n x) := by
  let e := FrameFrobeniusCompatibility.WittPolynomialFrameFrobeniusCompatibility.formEquiv p k σ n
  let f : (O).X n →ₛₗ[(ψ).toRingHom] (complex p k σ).X n :=
    ((comparisonIso p k σ).hom.f n).hom.comp ((F).f n)
  let g : (O).X n →ₛₗ[(ψ).toRingHom] (complex p k σ).X n :=
    ((complexMap p k σ).f n).comp ((comparisonIso p k σ).hom.f n).hom
  change f x = g x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (map_add f x y).trans ((congrArg₂ (fun a b => a + b) hx hy).trans (map_add g x y).symm)
  | tmul a ω =>
    have h := Polynomial.PolynomialAbsoluteFrobenius.rational_tmul p k σ n a ω
    change e.toLinearMap.baseChange K₀ ((F).f n (a ⊗ₜ[W] ω)) =
      formMap p k σ n (e.toLinearMap.baseChange K₀ (a ⊗ₜ[W] ω))
    exact (congrArg (e.toLinearMap.baseChange K₀) h).trans
      (congrArg (fun z => (ψ).toRingHom a ⊗ₜ[W] z)
        (FrameFrobeniusCompatibility.WittPolynomialFrameFrobeniusCompatibility.completed_naturality p k σ n ω))

def linearMap : complex p k σ ⟶ NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex
    (ψ).toRingHom (complex p k σ) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (complexMap p k σ)

def restrictedComparisonIso : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (ψ).toRingHom O ≅
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (ψ).toRingHom (complex p k σ) :=
  ((ModuleCat.restrictScalars (ψ).toRingHom).mapHomologicalComplex (.up ℕ)).mapIso (comparisonIso p k σ)

theorem linearMap_square : (comparisonIso p k σ).hom ≫ linearMap p k σ =
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap F ≫ (restrictedComparisonIso p k σ).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact LinearMap.ext (fun x => (intertwines p k σ n x).symm)

instance linearMap_quasiIso : QuasiIso (linearMap p k σ) := by
  have h : QuasiIso ((comparisonIso p k σ).hom ≫ linearMap p k σ) := by
    rw [linearMap_square]
    infer_instance
  let := h
  exact quasiIso_of_comp_left (comparisonIso p k σ).hom (linearMap p k σ)

def frobenius (n : ℕ) : (complex p k σ).homology n →ₛₗ[(ψ).toRingHom] (complex p k σ).homology n :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap (complexMap p k σ) n

theorem frobenius_bijective (n : ℕ) : Function.Bijective (frobenius p k σ n) := by
  let : QuasiIso (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (complexMap p k σ)) :=
    linearMap_quasiIso p k σ
  exact Semilinear.HomologyBijective.SemilinearHomologyBijective.homology_bijective (complexMap p k σ) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius
