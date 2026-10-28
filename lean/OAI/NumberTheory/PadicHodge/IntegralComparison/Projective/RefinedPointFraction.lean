import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Fraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulLeft
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedPointCoordinates

/-! # Refined Point Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.RefinedPointFraction

noncomputable section

/-! Both actual maps in the original common negative refinement are
retained in the supported point-class normalization. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
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
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Proj (homogeneousSubmodule σ R), U) s = f.ker.ideal ⟨U, hU⟩)
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule σ R), U) s t = (s₀ ≫ f).ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U) (List.ofFn s))
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U)
    (List.ofFn (Fin.append s t)))

abbrev comparison (q : ℕ) := by
  let hr := ProjectivePoint.KoszulMap.rightHomotopy s₀ f U hU i hi j B N e s t hs hst hreg hregst
  let hr' := KoszulPoint.HomCoordinates.homotopy Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) s t _ _ _ hr
  let hl := ProjectivePoint.KoszulLeft.leftHomotopy s₀ f U hU i hi j B N e s hs hreg
  let hl' := Koszul.NormalHomCoordinates.homotopy Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) s _ _ _ hl
  exact Koszul.RefinedPointCoordinates.comparison Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) (PrincipalPoint.Fraction.family U t) s t
      (PrincipalPoint.Fraction.units U hU t) _ _ _ _ _ hr' hl' q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.RefinedPointFraction
