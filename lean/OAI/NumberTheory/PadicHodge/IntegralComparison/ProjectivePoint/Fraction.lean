import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.HomCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction

/-! # Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Fraction.Comparison

noncomputable section

/-! The actual common negative-refinement map to the original point
coefficient sends its supported Koszul lift to the literal mixed
partial-fraction class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap
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

abbrev homology (q : ℕ) := by
  let h := KoszulMap.rightHomotopy s₀ f U hU i hi j B N e s t hs hst hreg hregst
  let hc := KoszulPoint.HomCoordinates.homotopy Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) s t _ _ _ h
  exact KoszulPoint.Map.Comparison.homology Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) (PrincipalPoint.Fraction.family U t) s t
      (PrincipalPoint.Fraction.units U hU t) _ _ _ hc q

abbrev class_eq
    (φ : Module.Dual Γ(Proj (homogeneousSubmodule σ R), U)
      (⋀[Γ(Proj (homogeneousSubmodule σ R), U)]^(c + m)
        (KoszulPartial.Fractions.ambient Γ(Proj (homogeneousSubmodule σ R), U) (c := c) (m := m)))) := by
  let h := KoszulMap.rightHomotopy s₀ f U hU i hi j B N e s t hs hst hreg hregst
  let hc := KoszulPoint.HomCoordinates.homotopy Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) s t _ _ _ h
  exact KoszulPoint.Map.Comparison.class_eq Γ(Proj (homogeneousSubmodule σ R), U)
    (Principal.SectionPresheaf.rings U hU) (PrincipalPoint.Fraction.family U t) s t
      (PrincipalPoint.Fraction.units U hU t) _ _ _ hc φ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Fraction.Comparison
