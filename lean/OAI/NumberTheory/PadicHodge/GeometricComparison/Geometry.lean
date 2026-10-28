import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter
import OAI.AlgebraicGeometry.Betti.Scheme
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Geometry -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

noncomputable section

/-! The input of GeometricComparison consists of actual abelian schemes and a generic-fiber
identification. Cohomology spaces are constructed from those schemes; no
cohomological comparison, finiteness, weights, or admissibility is stored. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

abbrev ringBase (R : Type) [CommRing R] := Spec (CommRingCat.of R)

def scalarBaseMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    ringBase S ⟶ ringBase R := Spec.map (CommRingCat.ofHom f)

structure AbelianH1Model (K : Type) [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime] (jq : K →+* ℚ_[q]) where
  dimension : ℕ
  variety : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dimension (ringBase K)
  integral : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dimension (ringBase ℤ_[q])
  genericIso :
    (integral.pullback (scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).scheme ≅
      (variety.pullback (scalarBaseMap jq)).scheme
  genericIso_group : IsMonHom genericIso.hom

namespace AbelianH1Model

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : AbelianH1Model K q jq)

def complexFiber (j : K →+* ℂ) := A.variety.pullback (scalarBaseMap j)

def localFiber := A.integral.pullback (scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))

def specialFiber := A.integral.pullback (scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))

/-- An endomorphism over K together with an actual extension over ℤ_q. -/
structure ExtendingEndomorphism where
  generic : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme
  integral : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.integral.scheme
  compatible :
    (Over.pullback (scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map
        integral.toMul.hom.hom ≫ A.genericIso.hom =
      A.genericIso.hom ≫
        (Over.pullback (scalarBaseMap jq)).map generic.toMul.hom.hom

def complexEndomorphism (j : K →+* ℂ) (f : A.ExtendingEndomorphism) :
    (A.complexFiber j).scheme ⟶ (A.complexFiber j).scheme :=
  (Over.pullback (scalarBaseMap j)).map f.generic.toMul.hom.hom

def localEndomorphism (f : A.ExtendingEndomorphism) :
    A.localFiber.scheme ⟶ A.localFiber.scheme :=
  (Over.pullback (scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map f.integral.toMul.hom.hom

def specialEndomorphism (f : A.ExtendingEndomorphism) :
    A.specialFiber.scheme ⟶ A.specialFiber.scheme :=
  (Over.pullback (scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).map
    f.integral.toMul.hom.hom

/-- Ordinary singular H¹ of the fixed complex fiber, with rational coefficients. -/
abbrev Betti (j : K →+* ℂ) :=
  AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (A.complexFiber j).scheme 1

def bettiPullback (j : K →+* ℂ) (f : A.ExtendingEndomorphism) :
    A.Betti j →ₗ[ℚ] A.Betti j :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (A.complexEndomorphism j f)).hom

/-- Algebraic de Rham hypercohomology over the number field. -/
abbrev AlgebraicDeRham :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology K A.variety.scheme 1

/-- Algebraic de Rham hypercohomology of the actual local generic fiber. -/
abbrev DeRham :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℚ_[q] A.localFiber.scheme 1

def Fil (i : ℤ) : Submodule ℚ_[q] A.DeRham :=
  AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℚ_[q] A.localFiber.scheme 1 i

theorem Fil_antitone : Antitone A.Fil :=
  AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration_antitone ℚ_[q] A.localFiber.scheme 1

/-- Cohomology's separate small-site construction, retained for the prerequisite adapter. -/
abbrev SmallCrystalline :=
  AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) A.specialFiber.scheme 1

/-- Rational crystalline H¹ on IntegralComparison's actual big Witt-vector crystalline site. -/
abbrev Crystalline := GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A.specialFiber.scheme

def crystallinePullback (f : A.ExtendingEndomorphism) :
    Module.End ℚ_[q] A.Crystalline :=
  GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (A.specialEndomorphism f)

/-- Pullback by the actual q-power Frobenius of the special fiber. -/
def crystallineFrobenius : Module.End ℚ_[q] A.Crystalline :=
  GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q
    (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) A.specialFiber.scheme)

/-- Independently constructed rational pro-étale H¹ of the geometric special fiber. -/
abbrev Etale (ℓ : ℕ) [Fact ℓ.Prime] :=
  IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ
    (IntegralComparison.Frobenius.Geometry.geometricFiber (L := AlgebraicClosure (ZMod q))
      A.specialFiber.scheme.hom) 1

def etaleFrobenius (ℓ : ℕ) [Fact ℓ.Prime] : A.Etale ℓ ≃ₗ[ℚ_[ℓ]] A.Etale ℓ :=
  IntegralComparison.Etale.Frobenius.geometricFrobeniusLinear ℓ q 1 (ZMod q)
    (by simp) A.specialFiber.scheme.hom 1

/-- The ℓ-adic characteristic polynomial is independent of crystalline
cohomology. Geometric finite-dimensionality is not bundled into the model. -/
def ellAdicFrobeniusPolynomial (ℓ : ℕ) [Fact ℓ.Prime]
    [FiniteDimensional ℚ_[ℓ] (A.Etale ℓ)] : Polynomial ℚ_[ℓ] :=
  LinearMap.charpoly (A.etaleFrobenius ℓ).toLinearMap

/-- Independent specification of an integral Weil polynomial, using only
the geometric special fiber's ℓ-adic cohomology and Frobenius. Existence
and finite-dimensionality are mathematical conclusions, not model fields. -/
def IsWeilPolynomial (ℓ : ℕ) [Fact ℓ.Prime] (P : Polynomial ℤ) : Prop :=
  ∃ hfinite : FiniteDimensional ℚ_[ℓ] (A.Etale ℓ),
    letI := hfinite
    A.ellAdicFrobeniusPolynomial ℓ = P.map (Int.castRingHom ℚ_[ℓ])

end AbelianH1Model

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
