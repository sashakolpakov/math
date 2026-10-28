import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomCohomologyNaturality

/-! # Intrinsic Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.IntrinsicSquare.Intrinsic

noncomputable section

/-! The literal native Hom-complex square defining the original
common-refinement dual map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (f : M ⟶ N) (n : ℕ)

omit [LinearOrder σ] in
theorem square :
    DualMap.map M N j B b hb f n ≫
      HomologicalComplex.homologyMap (Affine.HomCohomologyNaturality.nativeMap
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
        (Projective.NegativeRefinement.complex M N j B f)
        (Projective.NegativeResolution.complex M j B)
        (Projective.NegativeRefinement.leftHom M N j B f).chainMap) n =
      HomologicalComplex.homologyMap (Affine.HomCohomologyNaturality.nativeMap
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
        (Projective.NegativeRefinement.complex M N j B f)
        (Projective.NegativeResolution.complex N j B)
        (Projective.NegativeRefinement.rightHom M N j B f).chainMap) n :=
  DualMap.map_left M N j B b hb f n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.IntrinsicSquare.Intrinsic
