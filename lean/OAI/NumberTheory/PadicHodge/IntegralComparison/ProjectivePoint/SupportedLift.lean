import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SupportedLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal

/-! # Supported Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedLift

noncomputable section

/-! The duplicate-parameter supported lift on the original fixed
negative resolution of the iterated point direct image. Its
augmentation is transported by the genuine pushforward-composition
isomorphism, so the underlying resolution complex is unchanged. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable {Z X : Scheme.{u}} (s₀ : Z ⟶ X)
  (f : X ⟶ Proj (homogeneousSubmodule σ R))
  [IsClosedImmersion s₀] [IsClosedImmersion f]
  (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (j : σ) (B : ℕ)
  (N : (Proj (homogeneousSubmodule σ R)).Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Proj (homogeneousSubmodule σ R), U)] Γ(Proj (homogeneousSubmodule σ R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule σ R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule σ R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule σ R), U) s t =
    (s₀ ≫ f).ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U)
    (List.ofFn (Fin.append s t)))

local instance point_qc : (KoszulMap.point s₀ f).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent s₀ f
local instance point_finite : (KoszulMap.point s₀ f).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType s₀ f

abbrev augmentation := IntegralComparison.Projective.NegativeResolution.augmentation (KoszulMap.point s₀ f) j B ≫
  (ChainComplex.single₀ _).map (Closed.PointQuotientSquare.pointIso s₀ f).hom

instance augmentation_quasiIso : QuasiIso (augmentation s₀ f j B) := by
  dsimp only [augmentation]
  infer_instance

include hst in
omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] [IsClosedImmersion s₀] [IsClosedImmersion f] in
theorem equations : Koszul.OrientedTopCohomology.ideal
    Γ(Proj (homogeneousSubmodule σ R), U) (Fin.append s t) =
      (s₀ ≫ f).ker.ideal ⟨U, hU⟩ := by
  rw [← KoszulPoint.Ideal.append]
  exact hst

abbrev lift := by
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((KoszulMap.pointComplex s₀ f j B).X q)) :=
    KoszulMap.point_projective s₀ f U hU i hi j B q
  exact PrincipalPoint.SupportedLift.lift (s₀ ≫ f) U hU N e (KoszulMap.pointComplex s₀ f j B)
    (augmentation s₀ f j B) s t (equations s₀ f U hU s t hst) hreg

abbrev residue_forget (q : ℕ) := by
  letI (k : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((KoszulMap.pointComplex s₀ f j B).X k)) :=
    KoszulMap.point_projective s₀ f U hU i hi j B k
  exact PrincipalPoint.SupportedLift.residue_forget (s₀ ≫ f) U hU N e
    (KoszulMap.pointComplex s₀ f j B) (augmentation s₀ f j B) s t
      (equations s₀ f U hU s t hst) hreg q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedLift
