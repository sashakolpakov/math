import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.Betti.Affine
import OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.Betti.Scheme

noncomputable section

/-!
# Singular cohomology of the constructed complex-point space

The point space is the actual relative scheme-point carrier with the final
topology defined using all affine complex-point tests. On affine schemes it
has already been proved homeomorphic to the ordinary evaluation-topology
point space. This module connects that construction to genuine singular
cohomology, with affine compatibility and rational coefficient inclusion.

The global chart-recovery and smooth-manifold theorems are separate
obligations. No de Rham or algebraic cycle comparison is asserted here.
-/

open _root_.CategoryTheory Opposite

variable {R : Type} [Ring R]

/-- The constructed topological space of actual complex points of a scheme. -/
abbrev schemePointSpace (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : TopCat :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.obj X

/-- Genuine singular cohomology of the constructed complex-point space. -/
abbrev schemeBetti (M : ModuleCat R) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) : ModuleCat R :=
  AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M (schemePointSpace X) n

/-- Singular cohomology is contravariant in actual complex scheme morphisms. -/
def schemeBettiFunctor (M : ModuleCat R) (n : ℕ) :
    (Over Foundations.Scheme.ProjectiveSpace.complexBase)ᵒᵖ ⥤ ModuleCat R :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.op ⋙ AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor M n

/-- The pullback induced by the genuine continuous map on scheme points. -/
def schemeBettiMap (M : ModuleCat R) (n : ℕ)
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) : schemeBetti M Y n ⟶ schemeBetti M X n :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n

@[simp]
theorem schemeBettiFunctor_map (M : ModuleCat R) (n : ℕ)
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    (schemeBettiFunctor M n).map f.op = schemeBettiMap M n f := rfl

/-- The global construction recovers the already constructed affine Betti groups. -/
def schemeBettiAffineIso (M : ModuleCat R) (A : Type)
    [CommRing A] [Algebra ℂ A] (n : ℕ) :
    schemeBetti M (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) n ≅ Affine.affineBetti M A n :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor M n).mapIso
    (TopCat.isoOfHomeo (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A)).op

/-- The affine comparison is pullback along the proved point-space homeomorphism. -/
theorem schemeBettiAffineIso_hom (M : ModuleCat R) (A : Type)
    [CommRing A] [Algebra ℂ A] (n : ℕ) :
    (schemeBettiAffineIso M A n).hom =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M
        (TopCat.isoOfHomeo (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A)).hom n := rfl

/-- The actual rational-to-complex singular coefficient map on this point space. -/
def schemeBettiRationalInclusion (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    schemeBetti (ModuleCat.of ℚ ℚ) X n ⟶
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
        (schemeBetti (ModuleCat.of ℂ ℂ) X n) :=
  AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (schemePointSpace X) n

/-- Rational classes embed into the ordinary complex singular cohomology. -/
theorem schemeBettiRationalInclusion_injective (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    Function.Injective (schemeBettiRationalInclusion X n) :=
  AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_injective (schemePointSpace X) n

/-- The actual inclusion commutes with pullback along complex scheme morphisms. -/
theorem schemeBettiRationalInclusion_naturality
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (n : ℕ) :
    schemeBettiMap (ModuleCat.of ℚ ℚ) n f ≫ schemeBettiRationalInclusion X n =
      schemeBettiRationalInclusion Y n ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (schemeBettiMap (ModuleCat.of ℂ ℂ) n f) :=
  AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_naturality
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n

end

end OAI.AlgebraicGeometry.Betti.Scheme
