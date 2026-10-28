import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap

/-! # Dual Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualIso

noncomputable section

/-! An isomorphism of the original coefficient sheaves induces an
isomorphism through the actual common negative resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (e : M ≅ N)

include hb in
omit [LinearOrder σ] in
theorem right_quasiIso : QuasiIso (DualMap.rightMap M N j B b e.hom) := by
  let ε := Projective.NegativeRefinement.augmentation M N j B e.hom ≫
    (ChainComplex.single₀ _).map e.hom
  let : QuasiIso ε := by
    dsimp only [ε]
    infer_instance
  exact NegativeResolutionDualInvariance.quasiIso N
    (Projective.NegativeRefinement.complex M N j B e.hom)
    (Projective.NegativeResolution.complex N j B)
    (Projective.NegativeRefinement.term_above M N j B e.hom)
    (DualMap.fixed_term_above N j B)
    ε (Projective.NegativeResolution.augmentation N j B)
    (Projective.NegativeRefinement.rightHom M N j B e.hom).chainMap
    (Projective.NegativeRefinement.right_augmentation M N j B e.hom) b hb

def iso (q : ℕ) :
    (((DualMap.dualFunctor (R := R) j b).obj
      (op (Projective.NegativeResolution.complex N j B))).homology q) ≅
    (((DualMap.dualFunctor (R := R) j b).obj
      (op (Projective.NegativeResolution.complex M j B))).homology q) := by
  let : QuasiIso (DualMap.rightMap M N j B b e.hom) :=
    right_quasiIso M N j B b hb e
  exact isoOfQuasiIsoAt (DualMap.rightMap M N j B b e.hom) q ≪≫
    (DualMap.leftIso M N j B b hb e.hom q).symm

omit [LinearOrder σ] in
theorem iso_hom (q : ℕ) : (iso M N j B b hb e q).hom =
    DualMap.map M N j B b hb e.hom q := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualIso
