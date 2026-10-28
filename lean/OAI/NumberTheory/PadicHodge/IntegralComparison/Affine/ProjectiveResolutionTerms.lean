import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Projective Resolution Terms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionTerms

noncomputable section

/-! On affine opens inside a projective coordinate chart, the terms of
the genuine negative-twist resolution have projective section modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

instance sections_additive : (AffineOpen.InternalHom.sections U hU).Additive where
  map_add := rfl

def trivialSectionIso (L : X.Modules)
    (e : L.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    (AffineOpen.InternalHom.sections U hU).obj L ≅ ModuleCat.of Γ(X, U) Γ(X, U) := by
  let F := Scheme.Modules.restrictFunctor hU.isoSpec.inv
  let G := InternalHom.sections (R := Γ(X, U))
  let e' := F.mapIso e ≪≫ Scheme.Modules.restrictUnitIso hU.isoSpec.inv
  exact G.mapIso e' ≪≫ G.mapIso (tildeSelf (R := Γ(X, U))).symm ≪≫
    (tilde.isoTop (ModuleCat.of Γ(X, U) Γ(X, U))).symm

theorem trivial_projective (L : X.Modules)
    (e : L.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj L) :=
  Projective.of_iso (trivialSectionIso U hU L e).symm inferInstance

theorem coproduct_projective {I : Type} [Fintype I] (L : I → X.Modules)
    (hL : ∀ i, Projective ((AffineOpen.InternalHom.sections U hU).obj (L i))) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj (∐ L)) := by
  let (i : I) := hL i
  have hP : Projective (∐ fun i => (AffineOpen.InternalHom.sections U hU).obj (L i)) :=
    { factors := fun f e _ => ⟨Sigma.desc (fun i =>
        Projective.factorThru (Sigma.ι (fun i => (AffineOpen.InternalHom.sections U hU).obj (L i)) i ≫ f) e), by
          apply Sigma.hom_ext
          intro i
          simp⟩ }
  exact Projective.of_iso (PreservesCoproduct.iso (AffineOpen.InternalHom.sections U hU) L).symm hP

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (V : (Proj (homogeneousSubmodule σ R)).Opens) (hV : IsAffineOpen V)
  (i : σ) (hVi : V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

include i hVi

omit [Fintype σ] [LinearOrder σ] in
theorem negative_projective (j : σ) (a : ℕ) :
    Projective ((AffineOpen.InternalHom.sections V hV).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)) :=
  trivial_projective V hV _ (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hVi
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) i j a))

variable [IsNoetherianRing R]

omit [LinearOrder σ] in
theorem term_projective (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B n : ℕ) :
    Projective ((AffineOpen.InternalHom.sections V hV).obj ((IntegralComparison.Projective.NegativeResolution.complex M j B).X n)) := by
  let Q := IntegralComparison.Projective.NegativeResolution.presentation
    (IntegralComparison.Projective.NegativeResolution.state M j B n).module j B
  exact coproduct_projective V hV
    (fun t => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (Q.degree t))
    (fun t => negative_projective V hV i hVi j (Q.degree t))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionTerms
