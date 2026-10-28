import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology

/-! # Hecke Scalar -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
section

/-! The Hecke operators are rational linear combinations of actual extending
endomorphisms. Their presentations are geometric input; comparison properties
and preservation of Hodge filtration are not input. -/

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.deRhamPullback (f : A.ExtendingEndomorphism) : A.DeRham →ₗ[ℚ_[q]] A.DeRham :=
  GeometricComparison.DeRham.Int.pullback (A.localEndomorphism f) 1

def Geometry.AbelianH1Model.algebraicDeRhamPullback (f : A.ExtendingEndomorphism) :
    A.AlgebraicDeRham →ₗ[K] A.AlgebraicDeRham :=
  GeometricComparison.DeRham.Int.pullback f.generic.toMul.hom.hom 1

/-- The rational endomorphism algebra is the actual group-endomorphism
ring tensored with ℚ. Presentations record extending integral representatives. -/
structure Geometry.AbelianH1Model.HeckeRealization (H : Type) [CommRing H] [Algebra ℚ H] where
  action : H →ₐ[ℚ] AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.variety.scheme
  presentation : H → (A.ExtendingEndomorphism →₀ ℚ)
  represents : ∀ h,
    (presentation h).sum (fun f a => a ⊗ₜ[ℤ] f.generic) = action h

variable {H : Type} [CommRing H] [Algebra ℚ H]

def Geometry.AbelianH1Model.bettiHecke (j : K →+* ℂ) (ρ : A.HeckeRealization H) (h : H) :
    Module.End ℚ (A.Betti j) :=
  (ρ.presentation h).sum (fun f a => a • A.bettiPullback j f)

def Geometry.AbelianH1Model.deRhamHecke (ρ : A.HeckeRealization H) (h : H) : Module.End ℚ_[q] A.DeRham :=
  (ρ.presentation h).sum (fun f a => (a : ℚ_[q]) • A.deRhamPullback f)

/-- The fixed complex fiber's ordinary complex singular cohomology. -/
abbrev Geometry.AbelianH1Model.ComplexBetti (j : K →+* ℂ) :=
  AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) (A.complexFiber j).scheme 1

def Geometry.AbelianH1Model.complexBettiPullback (j : K →+* ℂ) (f : A.ExtendingEndomorphism) :
    Module.End ℂ (A.ComplexBetti j) :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (A.complexEndomorphism j f)).hom

def Geometry.AbelianH1Model.complexBettiHecke (j : K →+* ℂ) (ρ : A.HeckeRealization H) (h : H) :
    Module.End ℂ (A.ComplexBetti j) :=
  (ρ.presentation h).sum (fun f a => (a : ℂ) • A.complexBettiPullback j f)

def Geometry.AbelianH1Model.bettiHeckeSummand (j : K →+* ℂ) (ρ : A.HeckeRealization H)
    (χ : H → ℂ) : Submodule ℂ (A.ComplexBetti j) :=
  Linear.generalizedHeckeSummand (A.complexBettiHecke j ρ) χ

def Geometry.AbelianH1Model.deRhamHeckeSummand (ρ : A.HeckeRealization H)
    (χ : H → AlgebraicClosure ℚ_[q]) (L : Linear.FiniteHeckeCoefficientField q χ) :
    Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham) :=
  Linear.generalizedHeckeSummand
    (fun h => (A.deRhamHecke ρ h).baseChange L.field) L.character

/-- A closed projective embedding supplies the actual analytic Hodge
subspaces. It adds no assertion about their dimensions or comparison. -/
def Geometry.AbelianH1Model.smoothProjectiveFiber (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := (A.complexFiber j).scheme.left
  structureMap := (A.complexFiber j).scheme.hom
  projective := P
  smooth := inferInstance

/-- The ordinary weight-one Hodge filtration of this fixed complex variety. -/
def Geometry.AbelianH1Model.bettiFiltration (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (i : ℤ) : Submodule ℂ (A.ComplexBetti j) :=
  if i ≤ 0 then ⊤ else
    if i = 1 then (A.smoothProjectiveFiber j P).pureBettiSubspace 1 0 else ⊥

end

/-! Scalar-extension interfaces for the same algebraic de Rham object
over the number field. No geometric base-change or Betti comparison map
is postulated. The maps in the GeometricComparison conclusion have these domains. -/

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.algebraicFiltration (i : ℤ) : Submodule K A.AlgebraicDeRham :=
  AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration K A.variety.scheme 1 i

abbrev Geometry.AbelianH1Model.LocalAlgebraicDeRham :=
  letI : Algebra K ℚ_[q] := jq.toAlgebra
  ℚ_[q] ⊗[K] A.AlgebraicDeRham

abbrev Geometry.AbelianH1Model.ComplexAlgebraicDeRham (j : K →+* ℂ) :=
  letI : Algebra K ℂ := j.toAlgebra
  ℂ ⊗[K] A.AlgebraicDeRham

def Geometry.AbelianH1Model.localAlgebraicFiltration (i : ℤ) : Submodule ℚ_[q] A.LocalAlgebraicDeRham :=
  letI : Algebra K ℚ_[q] := jq.toAlgebra
  (A.algebraicFiltration i).baseChange ℚ_[q]

def Geometry.AbelianH1Model.complexAlgebraicFiltration (j : K →+* ℂ) (i : ℤ) :
    Submodule ℂ (A.ComplexAlgebraicDeRham j) :=
  letI : Algebra K ℂ := j.toAlgebra
  (A.algebraicFiltration i).baseChange ℂ

def Geometry.AbelianH1Model.localAlgebraicPullback (f : A.ExtendingEndomorphism) :
    Module.End ℚ_[q] A.LocalAlgebraicDeRham :=
  letI : Algebra K ℚ_[q] := jq.toAlgebra
  (A.algebraicDeRhamPullback f).baseChange ℚ_[q]

def Geometry.AbelianH1Model.complexAlgebraicPullback (j : K →+* ℂ) (f : A.ExtendingEndomorphism) :
    Module.End ℂ (A.ComplexAlgebraicDeRham j) :=
  letI : Algebra K ℂ := j.toAlgebra
  (A.algebraicDeRhamPullback f).baseChange ℂ

/-- This is the required type of a local geometric comparison, not an
assumed inhabitant or an equivalence built by identifying the spaces. -/
abbrev Geometry.AbelianH1Model.LocalComparisonMap := A.LocalAlgebraicDeRham →ₗ[ℚ_[q]] A.DeRham

/-- The complex comparison has genuine singular cohomology as its codomain. -/
abbrev Geometry.AbelianH1Model.BettiComparisonMap (j : K →+* ℂ) :=
  A.ComplexAlgebraicDeRham j →ₗ[ℂ] A.ComplexBetti j

end NumberTheory.PadicHodge.GeometricComparison

namespace NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! GeometricComparison's unproved target on independently constructed geometric objects.
All finiteness, comparisons, weight assertions and admissibility claims
are conclusions. This definition asserts none of them as a theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  (q : ℕ) [Fact q.Prime]
  (κ : K →+* AlgebraicClosure ℚ)
  (jComplex : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  (jq : K →+* ℚ_[q]) (A : Geometry.AbelianH1Model K q jq)
  (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
    (A.complexFiber (jComplex.comp κ)).scheme.hom)

/-- The exact scalar-conjugated eigensummand assertion. The complex variety
and its Hodge subspaces remain fixed; only the algebraic character changes. -/
def SummandComparison [FiniteDimensional ℚ_[q] A.DeRham]
    (Fil : Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham) : Prop :=
  ∀ χ : H →ₐ[ℚ] AlgebraicClosure ℚ,
    A.bettiHeckeSummand (jComplex.comp κ) ρ (fun h => jComplex (χ h)) ≠ ⊥ →
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      let χq : H → AlgebraicClosure ℚ_[q] := fun h => ι (σ (χ h))
      let χc : H → ℂ := fun h => jComplex (σ (χ h))
      ∃ L : Linear.FiniteHeckeCoefficientField q χq,
        let S : Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham) :=
          A.deRhamHeckeSummand ρ χq L
        let B : Submodule ℂ (A.ComplexBetti (jComplex.comp κ)) :=
          A.bettiHeckeSummand (jComplex.comp κ) ρ χc
        letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L.field S
        ∃ φS : S ≃ₗ[L.field] S,
          (∀ x : S, (φS x : L.field ⊗[ℚ_[q]] A.DeRham) =
            Linear.coefficientFrobenius L.field φdR.toLinearMap
              (x : L.field ⊗[ℚ_[q]] A.DeRham)) ∧
          Linear.WeaklyAdmissible q (Linear.coefficientSummandFiltration L.field Fil S)
            (φS.restrictScalars ℚ_[q]) ∧
          (∀ i : ℤ,
            Module.finrank L.field
                (S ⊓ Linear.coefficientFiltration L.field A.Fil i :
                  Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham)) =
              Module.finrank ℂ
                (B ⊓ A.bettiFiltration (jComplex.comp κ) P i :
                  Submodule ℂ (A.ComplexBetti (jComplex.comp κ))))

/-- Full comparison properties after the geometric finiteness assertions. -/
def FiniteComparison
    [FiniteDimensional ℚ_[q] A.DeRham] [FiniteDimensional ℚ_[q] A.Crystalline]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
    (Fil : Linear.FiniteFiltration ℚ_[q] A.DeRham),
    φ.toLinearMap = A.crystallineFrobenius ∧
    Fil.step = A.Fil ∧
    let φdR := cmp.symm.trans (φ.trans cmp)
    Linear.WeaklyAdmissible q Fil φdR ∧
    (∀ f : A.ExtendingEndomorphism,
      (∀ x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) ∧
      (∀ x, φ (A.crystallinePullback f x) = A.crystallinePullback f (φ x)) ∧
      (∀ i : ℤ, (A.Fil i).map (A.deRhamPullback f) ≤ A.Fil i)) ∧
    (∃ W : Polynomial ℤ,
      A.IsWeilPolynomial ℓ W ∧
      LinearMap.charpoly A.crystallineFrobenius = W.map (Int.castRingHom ℚ_[q]) ∧
      ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ = Real.sqrt (q : ℝ)) ∧
    (∃ (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
      (bettiCmp : A.ComplexAlgebraicDeRham (jComplex.comp κ) ≃ₗ[ℂ] A.ComplexBetti (jComplex.comp κ)),
      (∀ f : A.ExtendingEndomorphism,
        (∀ x, localCmp (A.localAlgebraicPullback f x) = A.deRhamPullback f (localCmp x)) ∧
        (∀ x, bettiCmp (A.complexAlgebraicPullback (jComplex.comp κ) f x) =
          A.complexBettiPullback (jComplex.comp κ) f (bettiCmp x))) ∧
      (∀ i : ℤ, (A.localAlgebraicFiltration i).map localCmp.toLinearMap = A.Fil i) ∧
      (∀ i : ℤ, (A.complexAlgebraicFiltration (jComplex.comp κ) i).map bettiCmp.toLinearMap =
        A.bettiFiltration (jComplex.comp κ) P i)) ∧
    SummandComparison q κ jComplex ι jq A H ρ P Fil φdR

/-- Statement-only target. The numerical operations are used only after
finite-dimensionality has been asserted in the conclusion. -/
def ComparisonTarget (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
      letI := hD
      letI := hC
      FiniteComparison q κ jComplex ι jq A H ρ P ℓ

end NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

end

end OAI
