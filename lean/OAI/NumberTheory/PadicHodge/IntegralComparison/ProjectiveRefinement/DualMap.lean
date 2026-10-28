import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeResolutionDualInvariance
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeRefinement

/-! # Dual Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap

noncomputable section

/-! A morphism of coherent sheaves induces an actual map of the
cohomology sheaves of their dual negative resolutions. The construction
uses the two maps from a common resolution and inverts only the dual
quasi-isomorphism of its identity lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (f : M ⟶ N)

abbrev dualFunctor := Affine.LocalDualInvariance.functor
  (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)

omit [LinearOrder σ] in
theorem fixed_term_above (q : ℕ) :
    NegativeTerms.Above ((Projective.NegativeResolution.complex M j B).X q) j B :=
  NegativeTerms.presentation (Projective.NegativeResolution.presentation
    (Projective.NegativeResolution.state M j B q).module j B)

def leftMap := (dualFunctor (R := R) j b).map
  (Projective.NegativeRefinement.leftHom M N j B f).chainMap.op

def rightMap := (dualFunctor (R := R) j b).map
  (Projective.NegativeRefinement.rightHom M N j B f).chainMap.op

omit [LinearOrder σ] in
include hb in
theorem left_quasiIso : QuasiIso (leftMap M N j B b f) :=
  NegativeResolutionDualInvariance.quasiIso M
    (Projective.NegativeRefinement.complex M N j B f)
    (Projective.NegativeResolution.complex M j B)
    (Projective.NegativeRefinement.term_above M N j B f)
    (fixed_term_above M j B)
    (Projective.NegativeRefinement.augmentation M N j B f)
    (Projective.NegativeResolution.augmentation M j B)
    (Projective.NegativeRefinement.leftHom M N j B f).chainMap
    (Projective.NegativeRefinement.left_augmentation M N j B f) b hb

def leftIso (q : ℕ) := by
  let := left_quasiIso M N j B b hb f
  exact isoOfQuasiIsoAt (leftMap M N j B b f) q

def map (q : ℕ) :
    (((dualFunctor (R := R) j b).obj (op (Projective.NegativeResolution.complex N j B))).homology q) ⟶
      (((dualFunctor (R := R) j b).obj (op (Projective.NegativeResolution.complex M j B))).homology q) :=
  HomologicalComplex.homologyMap (rightMap M N j B b f) q ≫ (leftIso M N j B b hb f q).inv

omit [LinearOrder σ] in
@[reassoc]
theorem map_left (q : ℕ) : DualMap.map M N j B b hb f q ≫ (leftIso M N j B b hb f q).hom =
    HomologicalComplex.homologyMap (rightMap M N j B b f) q := by
  simp only [DualMap.map, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap
