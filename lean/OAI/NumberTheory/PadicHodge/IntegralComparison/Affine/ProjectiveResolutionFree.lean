import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.DirectSum.Finite

/-! # Projective Resolution Free -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionFree

noncomputable section

/-! The original finite negative-twist resolution has finite free
section modules on every affine subopen of a projective coordinate chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionTerms

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

theorem trivial_free (L : X.Modules)
    (e : L.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj L) :=
  Module.Free.of_equiv (ProjectiveResolutionTerms.trivialSectionIso U hU L e).toLinearEquiv.symm

theorem trivial_finite (L : X.Modules)
    (e : L.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj L) :=
  Module.Finite.equiv (ProjectiveResolutionTerms.trivialSectionIso U hU L e).toLinearEquiv.symm

theorem coproduct_free {I : Type} [Fintype I] (L : I → X.Modules)
    (hL : ∀ i, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L i))) :
    Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (∐ L)) := by
  classical
  let (i : I) := hL i
  let e := PreservesCoproduct.iso (AffineOpen.InternalHom.sections U hU) L ≪≫
    ModuleCat.coprodIsoDirectSum (fun i => (AffineOpen.InternalHom.sections U hU).obj (L i))
  exact Module.Free.of_equiv e.toLinearEquiv.symm

theorem coproduct_finite {I : Type} [Fintype I] (L : I → X.Modules)
    (hL : ∀ i, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L i))) :
    Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (∐ L)) := by
  classical
  let (i : I) := hL i
  let e := PreservesCoproduct.iso (AffineOpen.InternalHom.sections U hU) L ≪≫
    ModuleCat.coprodIsoDirectSum (fun i => (AffineOpen.InternalHom.sections U hU).obj (L i))
  exact Module.Finite.equiv e.toLinearEquiv.symm

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (V : (Proj (homogeneousSubmodule σ R)).Opens) (hV : IsAffineOpen V)
  (i : σ) (hVi : V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

include i hVi

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem negative_free (j : σ) (a : ℕ) :
    Module.Free Γ(Proj (homogeneousSubmodule σ R), V)
      ((AffineOpen.InternalHom.sections V hV).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)) :=
  trivial_free V hV _ (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hVi
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) i j a))

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem negative_finite (j : σ) (a : ℕ) :
    Module.Finite Γ(Proj (homogeneousSubmodule σ R), V)
      ((AffineOpen.InternalHom.sections V hV).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)) :=
  trivial_finite V hV _ (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hVi
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) i j a))

variable (M : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B q : ℕ)

omit [LinearOrder σ] in
theorem term_free : Module.Free Γ(Proj (homogeneousSubmodule σ R), V)
    ((AffineOpen.InternalHom.sections V hV).obj ((Projective.NegativeResolution.complex M j B).X q)) := by
  let Q := Projective.NegativeResolution.presentation
    (Projective.NegativeResolution.state M j B q).module j B
  exact coproduct_free V hV
    (fun t => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (Q.degree t))
    (fun t => negative_free V hV i hVi j (Q.degree t))

omit [LinearOrder σ] in
theorem term_finite : Module.Finite Γ(Proj (homogeneousSubmodule σ R), V)
    ((AffineOpen.InternalHom.sections V hV).obj ((Projective.NegativeResolution.complex M j B).X q)) := by
  let Q := Projective.NegativeResolution.presentation
    (Projective.NegativeResolution.state M j B q).module j B
  exact coproduct_finite V hV
    (fun t => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (Q.degree t))
    (fun t => negative_finite V hV i hVi j (Q.degree t))

include hV in
omit [LinearOrder σ] in
theorem actual_term_free : Module.Free Γ(Proj (homogeneousSubmodule σ R), V)
    (((Projective.NegativeResolution.complex M j B).X q).val.obj (.op V)) := by
  let := term_free V hV i hVi M j B q
  exact Module.Free.of_equiv
    (ChartSections.iso V hV ((Projective.NegativeResolution.complex M j B).X q)).toLinearEquiv.symm

include hV in
omit [LinearOrder σ] in
theorem actual_term_finite : Module.Finite Γ(Proj (homogeneousSubmodule σ R), V)
    (((Projective.NegativeResolution.complex M j B).X q).val.obj (.op V)) := by
  let := term_finite V hV i hVi M j B q
  exact Module.Finite.equiv
    (ChartSections.iso V hV ((Projective.NegativeResolution.complex M j B).X q)).toLinearEquiv.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionFree
