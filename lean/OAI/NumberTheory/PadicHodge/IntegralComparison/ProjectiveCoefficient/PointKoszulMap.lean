import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.CoefficientCoordinates

/-! # Point Koszul Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.PointKoszulMap

noncomputable section

/-! The actual common negative refinement for any coherent coefficient
map to the fixed point sheaf agrees with its canonical local resolution
lift on the entire principal diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable {Z X : Scheme.{u}} (s₀ : Z ⟶ X)
  (f : X ⟶ Proj (homogeneousSubmodule σ R))
  [IsClosedImmersion s₀] [IsClosedImmersion f]
  (M : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType]

abbrev point := ProjectivePoint.KoszulMap.point s₀ f
local instance point_qc : (point s₀ f).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent s₀ f
local instance point_finite : (point s₀ f).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType s₀ f

variable (v : M ⟶ point s₀ f)
  (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (j : σ) (B : ℕ)

abbrev common := IntegralComparison.Projective.NegativeRefinement.complex M (point s₀ f) j B v
abbrev fixed := IntegralComparison.Projective.NegativeResolution.complex M j B
abbrev pointComplex := IntegralComparison.Projective.NegativeResolution.complex (point s₀ f) j B

local instance common_qc (q : ℕ) : ((common s₀ f M v j B).X q).IsQuasicoherent :=
  IntegralComparison.Projective.NegativeRefinement.term_quasicoherent M (point s₀ f) j B v q

include hi in
omit [LinearOrder σ] in
theorem common_projective (q : ℕ) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj ((common s₀ f M v j B).X q)) :=
  NegativeAffineProjectivity.of_above U hU i hi
    (IntegralComparison.Projective.NegativeRefinement.term_above M (point s₀ f) j B v q)

include hi in
omit [LinearOrder σ] in
theorem fixed_projective (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((fixed M j B).X q)) :=
  Affine.ProjectiveResolutionTerms.term_projective U hU i hi M j B q

include hi in
omit [LinearOrder σ] in
theorem point_projective (q : ℕ) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj ((pointComplex s₀ f j B).X q)) :=
  Affine.ProjectiveResolutionTerms.term_projective U hU i hi (point s₀ f) j B q

variable (N : (Proj (homogeneousSubmodule σ R)).Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Proj (homogeneousSubmodule σ R), U)]
    Γ(Proj (homogeneousSubmodule σ R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule σ R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule σ R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule σ R), U) s t =
    (s₀ ≫ f).ker.ideal ⟨U, hU⟩)
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U)
    (List.ofFn (Fin.append s t)))
  (T : ModuleCat.{u} Γ(Proj (homogeneousSubmodule σ R), U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T) (PM : ProjectiveResolution T)

def coefficient : T ⟶ ModuleCat.of Γ(Proj (homogeneousSubmodule σ R), U)
    (Γ(Proj (homogeneousSubmodule σ R), U) ⧸ KoszulPartial.Resolution.pointIdeal _ s t) :=
  eM.inv ≫ (AffineOpen.InternalHom.sections U hU).map v ≫
    (Closed.PointQuotientSquare.pointQuotient s₀ f U hU s t hst).hom

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] [M.IsQuasicoherent] [M.IsFiniteType] in
theorem coefficient_square : (AffineOpen.InternalHom.sections U hU).map v ≫
    (Closed.PointQuotientSquare.pointQuotient s₀ f U hU s t hst).hom =
      eM.hom ≫ coefficient s₀ f M v U hU s t hst T eM := by
  simp only [coefficient, Iso.hom_inv_id_assoc]

abbrev pointLift := ProjectiveResolution.lift
  (coefficient s₀ f M v U hU s t hst T eM) PM (KoszulPartial.Resolution.pointResolution _ s t hregst)

abbrev rightHomotopy := by
  letI (q : ℕ) := common_projective s₀ f M v U hU i hi j B q
  letI (q : ℕ) := point_projective s₀ f U hU i hi j B q
  let ε := IntegralComparison.Projective.NegativeRefinement.augmentation M (point s₀ f) j B v
  let ε' := IntegralComparison.Projective.NegativeResolution.augmentation (point s₀ f) j B
  let r := (IntegralComparison.Projective.NegativeRefinement.rightHom M (point s₀ f) j B v).chainMap
  let eP := Closed.PointQuotientSquare.pointQuotient s₀ f U hU s t hst
  let b := coefficient s₀ f M v U hU s t hst T eM
  let hv := Principal.ResolutionAugmentation.square U hU M (common s₀ f M v j B) ε T eM
    (point s₀ f) (pointComplex s₀ f j B) ε' _ eP r v b
    (IntegralComparison.Projective.NegativeRefinement.right_augmentation M (point s₀ f) j B v)
    (coefficient_square s₀ f M v U hU s t hst T eM)
  exact Principal.Resolution.Comparison.naturality U hU N e
    M (common s₀ f M v j B) ε T eM PM
    (point s₀ f) (pointComplex s₀ f j B) ε' _ eP (KoszulPartial.Resolution.pointResolution _ s t hregst)
    r b (pointLift s₀ f M v U hU s t hst hregst T eM PM) hv
    (ProjectiveResolution.lift_commutes b PM (KoszulPartial.Resolution.pointResolution _ s t hregst))

abbrev rightCoordinates :=
  KoszulPoint.CoefficientCoordinates.homotopy Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) s t hregst T PM
    (pointLift s₀ f M v U hU s t hst hregst T eM PM) _ _ _
    (rightHomotopy s₀ f M v U hU i hi j B N e s t hst hregst T eM PM)

abbrev leftHomotopy := by
  letI (q : ℕ) := common_projective s₀ f M v U hU i hi j B q
  letI (q : ℕ) := fixed_projective M U hU i hi j B q
  let ε := IntegralComparison.Projective.NegativeRefinement.augmentation M (point s₀ f) j B v
  let ε' := IntegralComparison.Projective.NegativeResolution.augmentation M j B
  let l := (IntegralComparison.Projective.NegativeRefinement.leftHom M (point s₀ f) j B v).chainMap
  let hv := Principal.ResolutionAugmentation.square U hU M (common s₀ f M v j B) ε T eM
    M (fixed M j B) ε' T eM l (𝟙 M) (𝟙 T)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
      IntegralComparison.Projective.NegativeRefinement.left_augmentation M (point s₀ f) j B v)
    (by simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  exact Principal.Resolution.Comparison.naturality U hU N e
    M (common s₀ f M v j B) ε T eM PM M (fixed M j B) ε' T eM PM
    l (𝟙 T) (𝟙 PM.complex) hv
    (by simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.PointKoszulMap
