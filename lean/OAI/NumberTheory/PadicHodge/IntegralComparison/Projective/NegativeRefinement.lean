import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeCommonRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTerms

/-! # Negative Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeRefinement

noncomputable section

/-! Every morphism of coherent sheaves on projective space has a
literal common negative resolution mapping to the two fixed resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (j : σ) (B : ℕ)

instance fixed_object_quasicoherent (n : ℕ) :
    ((NegativeResolution.tower M j B).object n).IsQuasicoherent :=
  inferInstanceAs (NegativeResolution.state M j B n).module.IsQuasicoherent

instance fixed_term_quasicoherent (n : ℕ) :
    ((NegativeResolution.tower M j B).term n).IsQuasicoherent :=
  inferInstanceAs (NegativeResolution.presentation
    (NegativeResolution.state M j B n).module j B).source.IsQuasicoherent

instance fixed_term_finiteType (n : ℕ) :
    ((NegativeResolution.tower M j B).term n).IsFiniteType :=
  inferInstanceAs (NegativeResolution.presentation
    (NegativeResolution.state M j B n).module j B).source.IsFiniteType

variable (f : M ⟶ N)

def tower := NegativeCommonRefinement.tower
  (NegativeResolution.tower M j B) (NegativeResolution.tower N j B)
  j B M (𝟙 M) f

def leftHom : KernelTowerMap.Hom (tower M N j B f) (NegativeResolution.tower M j B) :=
  NegativeCommonRefinement.leftHom
    (NegativeResolution.tower M j B)
    (NegativeResolution.tower N j B) j B M (𝟙 M) f

def rightHom : KernelTowerMap.Hom (tower M N j B f) (NegativeResolution.tower N j B) :=
  NegativeCommonRefinement.rightHom
    (NegativeResolution.tower M j B)
    (NegativeResolution.tower N j B) j B M (𝟙 M) f

abbrev complex := (tower M N j B f).complex

def augmentation : NegativeRefinement.complex M N j B f ⟶ (ChainComplex.single₀ _).obj M :=
  (tower M N j B f).augmentation

instance augmentation_quasiIso : QuasiIso (NegativeRefinement.augmentation M N j B f) :=
  inferInstanceAs (QuasiIso (tower M N j B f).augmentation)

instance left_quasiIso : QuasiIso (leftHom M N j B f).chainMap :=
  inferInstanceAs (QuasiIso (NegativeCommonRefinement.leftHom
    (NegativeResolution.tower M j B) (NegativeResolution.tower N j B)
    j B M (𝟙 M) f).chainMap)

omit [LinearOrder σ] in
theorem left_augmentation : (leftHom M N j B f).chainMap ≫
    NegativeResolution.augmentation M j B = NegativeRefinement.augmentation M N j B f := by
  have h := (leftHom M N j B f).augmentation
  change (leftHom M N j B f).chainMap ≫
    NegativeResolution.augmentation M j B =
      NegativeRefinement.augmentation M N j B f ≫ (ChainComplex.single₀ _).map (𝟙 M) at h
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
    h

omit [LinearOrder σ] in
theorem right_augmentation : (rightHom M N j B f).chainMap ≫
    NegativeResolution.augmentation N j B =
      NegativeRefinement.augmentation M N j B f ≫ (ChainComplex.single₀ _).map f :=
  (rightHom M N j B f).augmentation

omit [LinearOrder σ] in
theorem term_above (n : ℕ) : NegativeTerms.Above ((tower M N j B f).term n) j B :=
  NegativeTerms.presentation ((NegativeCommonRefinement.state
    (NegativeResolution.tower M j B) (NegativeResolution.tower N j B)
    j B M (𝟙 M) f n).cover j B)

instance object_quasicoherent (n : ℕ) : ((tower M N j B f).object n).IsQuasicoherent :=
  inferInstanceAs (NegativeCommonRefinement.state
    (NegativeResolution.tower M j B) (NegativeResolution.tower N j B)
    j B M (𝟙 M) f n).module.IsQuasicoherent

instance term_quasicoherent (n : ℕ) : ((tower M N j B f).term n).IsQuasicoherent :=
  NegativeTerms.quasicoherent (term_above M N j B f n)

instance term_finiteType (n : ℕ) : ((tower M N j B f).term n).IsFiniteType :=
  NegativeTerms.finiteType (term_above M N j B f n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeRefinement
