import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointQuotientSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ResolutionAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeAffineProjectivity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapPureTrace

/-! # Koszul Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap

noncomputable section

/-! The original common negative refinement of the map to a section
is the canonical normal-to-point Koszul map on the entire principal
diagram, by an augmentation-normalized cochain homotopy. -/
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
  (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (j : σ) (B : ℕ)

abbrev scalar := Principal.ClosedQuotient.directImage f
abbrev point := Cech.StructurePullbackUnit.coefficients s₀ f
abbrev quotientMap := Cech.StructurePullbackUnit.sheafMap s₀ f

local instance scalar_qc : (scalar f).IsQuasicoherent :=
  IntegralComparison.Projective.ClosedImmersionPurity.directImage_quasicoherent f
local instance scalar_finite : (scalar f).IsFiniteType :=
  IntegralComparison.Projective.ClosedImmersionPurity.directImage_finiteType f
local instance point_qc : (point s₀ f).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent s₀ f
local instance point_finite : (point s₀ f).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType s₀ f

abbrev common := IntegralComparison.Projective.NegativeRefinement.complex (scalar f) (point s₀ f) j B (quotientMap s₀ f)
abbrev pointComplex := IntegralComparison.Projective.NegativeResolution.complex (point s₀ f) j B

local instance common_qc (q : ℕ) : ((common s₀ f j B).X q).IsQuasicoherent :=
  IntegralComparison.Projective.NegativeRefinement.term_quasicoherent (scalar f) (point s₀ f) j B (quotientMap s₀ f) q
include hi in
omit [LinearOrder σ] in
theorem common_projective (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((common s₀ f j B).X q)) :=
  NegativeAffineProjectivity.of_above U hU i hi
    (IntegralComparison.Projective.NegativeRefinement.term_above (scalar f) (point s₀ f) j B (quotientMap s₀ f) q)
include hi in
omit [LinearOrder σ] in
theorem point_projective (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((pointComplex s₀ f j B).X q)) :=
  Affine.ProjectiveResolutionTerms.term_projective U hU i hi (point s₀ f) j B q

variable (N : (Proj (homogeneousSubmodule σ R)).Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Proj (homogeneousSubmodule σ R), U)] Γ(Proj (homogeneousSubmodule σ R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule σ R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule σ R), U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Proj (homogeneousSubmodule σ R), U) s = f.ker.ideal ⟨U, hU⟩)
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule σ R), U) s t = (s₀ ≫ f).ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U) (List.ofFn s))
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U) (List.ofFn (Fin.append s t)))

abbrev rightHomotopy := by
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((common s₀ f j B).X q)) :=
    common_projective s₀ f U hU i hi j B q
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((pointComplex s₀ f j B).X q)) :=
    point_projective s₀ f U hU i hi j B q
  let ε := IntegralComparison.Projective.NegativeRefinement.augmentation (scalar f) (point s₀ f) j B (quotientMap s₀ f)
  let ε' := IntegralComparison.Projective.NegativeResolution.augmentation (point s₀ f) j B
  let v := (IntegralComparison.Projective.NegativeRefinement.rightHom (scalar f) (point s₀ f) j B (quotientMap s₀ f)).chainMap
  let eM := Principal.OrientedResidue.quotientIso f U hU s hs
  let eP := Closed.PointQuotientSquare.pointQuotient s₀ f U hU s t hst
  let hv := Principal.ResolutionAugmentation.square U hU (scalar f) (common s₀ f j B) ε _ eM
    (point s₀ f) (pointComplex s₀ f j B) ε' _ eP v (quotientMap s₀ f) (KoszulPartial.Resolution.quotient _ s t)
    (IntegralComparison.Projective.NegativeRefinement.right_augmentation (scalar f) (point s₀ f) j B (quotientMap s₀ f))
    (Closed.PointQuotientSquare.square s₀ f U hU s t hs hst)
  exact Principal.Resolution.Comparison.naturality U hU N e
    (scalar f) (common s₀ f j B) ε _ eM (KoszulPartial.Resolution.normalResolution _ s hreg)
    (point s₀ f) (pointComplex s₀ f j B) ε' _ eP (KoszulPartial.Resolution.pointResolution _ s t hregst)
    v (KoszulPartial.Resolution.quotient _ s t) (KoszulPartial.Resolution.inclusion _ s t) hv (KoszulPartial.Resolution.augmentation _ s t hreg hregst)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap
