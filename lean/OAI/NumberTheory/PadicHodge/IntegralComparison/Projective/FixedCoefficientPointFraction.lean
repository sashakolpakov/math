import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.PointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientSectionEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SectionQuotient

/-! # Fixed Coefficient Point Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FixedCoefficientPointFraction

noncomputable section

/-! Evaluating the image of the original fixed trace-one point class
on an actual coefficient vector yields its section value times the same
scalar mixed fraction as the scalar coefficient branch. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType]
  (v : M ⟶ ProjectivePoint.KoszulMap.point s₀ f)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (s₀ ≫ f) ⁻¹ᵁ U)
  (i : Fin (n+2)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (e : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (ProjectivePoint.Survivor.chart (R := R)) (n+2), U) ≃ₗ[
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)]
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (s₀ ≫ f).ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn s))
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))
  (C : Type u) [AddCommGroup C] [Module Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) C]
  [Module (Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) ⧸ KoszulPartial.Resolution.normalIdeal _ s) C]
  [IsScalarTower Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) ⧸ KoszulPartial.Resolution.normalIdeal _ s) C]
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) C)
  (PM : ProjectiveResolution (ModuleCat.of Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) C))
  (x : C)

local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U

abbrev ε := (ProjectiveCoefficient.PointKoszulMap.coefficient s₀ f M v U hU s t hst _ eM).hom
abbrev e₀ := KoszulPoint.SectionQuotient.equiv R
  Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t
  (ProjectivePoint.ScalarFraction.pointQuotient f s₀ hbase U hU hcontains s t hst)
abbrev scalar := Koszul.CoefficientSectionEvaluation.scalar R
  Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t
  (e₀ f s₀ hbase U hU hcontains s t hst) C (ε f s₀ M v U hU s t hst C eM) x

abbrev weight := Koszul.CoefficientSectionEvaluation.weight R
  Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t
  (e₀ f s₀ hbase U hU hcontains s t hst) C (ε f s₀ M v U hU s t hst C eM) x

variable [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (hcm : c+m=n+1)

abbrev normalization := ProjectiveCoefficient.PointFraction.comparison
  f s₀ hbase B hB M v U hU hcontains i hi e s t hst hreg hregst _ eM PM
  (Koszul.CoefficientPointFraction.vector Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s C x)
  (scalar f s₀ hbase M v U hU hcontains s t hst C eM x)
  (weight f s₀ hbase M v U hU hcontains s t hst C eM x)
  (ProjectivePoint.LocalCoordinates.pointAt f s₀ hbase B hB U hU s t hst hcm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FixedCoefficientPointFraction
