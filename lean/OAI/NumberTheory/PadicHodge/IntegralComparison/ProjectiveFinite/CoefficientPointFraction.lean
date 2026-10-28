import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FixedCoefficientPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.PointCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.QuotientAction

/-! # Coefficient Point Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPointFraction

noncomputable section

/-! The actual finite coefficient sheaf and actual section quotient,
on the original negative resolution, satisfy the fixed-point fraction
formula. All coefficient actions and local projective resolutions are
constructed from the given geometric map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y) [IsClosedImmersion (s₀ ≫ f)]
  (hbase : (s₀ ≫ f) ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ ((s₀ ≫ f) ≫ i) ⁻¹ᵁ U)
  (j : Fin (n+2)) (hj : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
  (e : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (ProjectivePoint.Survivor.chart (R := R)) (n+2), U) ≃ₗ[
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)]
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s = i.ker.ideal ⟨U,hU⟩)
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    ((s₀ ≫ f) ≫ i).ker.ideal ⟨U,hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn s))
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))

abbrev coefficients := Cech.StructurePullbackUnit.coefficients f i
local instance coefficients_qc : (coefficients f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i
local instance coefficients_finite : (coefficients f i).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f i

abbrev source := Projective.NegativeResolution.complex (coefficients f i) (ProjectivePoint.Survivor.chart (R := R)) B
abbrev augmentation := Projective.NegativeResolution.augmentation (coefficients f i) (ProjectivePoint.Survivor.chart (R := R)) B

abbrev resolution := by
  letI (q : ℕ) := Affine.ProjectiveResolutionTerms.term_projective U hU j hj
    (coefficients f i) (ProjectivePoint.Survivor.chart (R := R)) B q
  exact Principal.Resolution.Comparison.resolution U hU (coefficients f i)
    (source f i B) (augmentation f i B) _ (Finite.FlatCoefficientSections.chartIso f i U hU)

variable [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (hcm : c+m=n+1)

abbrev normalization (x : Finite.FlatCoefficientSections.coefficientRing f i U) := by
  letI := FiniteCoefficient.QuotientAction.algebra f i U hU s hs
  letI := FiniteCoefficient.QuotientAction.tower f i U hU s hs
  exact Projective.FixedCoefficientPointFraction.normalization i (s₀ ≫ f) hbase B hB
    (coefficients f i) (Cech.SectionCoefficientUnit.sheafMap s₀ f i)
    U hU hcontains j hj e s t hst hreg hregst (Finite.FlatCoefficientSections.coefficientRing f i U)
    (Finite.FlatCoefficientSections.chartIso f i U hU) (resolution f i B U hU j hj) x hcm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPointFraction
