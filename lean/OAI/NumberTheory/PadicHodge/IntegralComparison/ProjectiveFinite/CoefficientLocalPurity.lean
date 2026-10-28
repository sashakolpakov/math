import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FiniteProjectivePurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.CoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomCoherence

/-! # Coefficient Local Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientLocalPurity

noncomputable section

/-! Native affine purity for the original negative resolution of the
finite flat coefficient algebra on a smooth closed subscheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
  (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
  [IsLocallyNoetherian X]

abbrev coefficients := Cech.StructurePullbackUnit.coefficients f i

instance coefficients_quasicoherent : (coefficients f i).IsQuasicoherent :=
  IntegralComparison.Finite.MapPureTrace.coefficients_quasicoherent f i
instance coefficients_finiteType : (coefficients f i).IsFiniteType :=
  IntegralComparison.Finite.MapPureTrace.coefficients_finiteType f i

variable (j : σ) (B b : ℕ)
abbrev source := IntegralComparison.Projective.NegativeResolution.complex (coefficients f i) j B

instance source_quasicoherent (q : ℕ) : ((CoefficientLocalPurity.source f i j B).X q).IsQuasicoherent :=
  inferInstanceAs ((IntegralComparison.Projective.NegativeResolution.presentation
    (IntegralComparison.Projective.NegativeResolution.state (coefficients f i) j B q).module j B).source.IsQuasicoherent)

def internalComplex := Affine.LinearResolutionPurity.internalComplex
  (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (CoefficientLocalPurity.source f i j B)

variable (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (k : σ) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
attribute [local instance] IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra

def quotientIso (rs : List Γ(Proj (homogeneousSubmodule σ R), U))
    (hrs : RingHom.ker (i.app U).hom = Ideal.ofList rs) :
    ProjectiveResolution.DualPurity.quotient Γ(Proj (homogeneousSubmodule σ R), U) rs ≅
      ModuleCat.of Γ(Proj (homogeneousSubmodule σ R), U) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) :=
  Closed.ImmersionQuotientSections.listQuotientIso i U hU rs hrs

include hU k hUk in
omit [LinearOrder σ] in
theorem exactAt (rs : List Γ(Proj (homogeneousSubmodule σ R), U))
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U) rs)
    (hrs : RingHom.ker (i.app U).hom = Ideal.ofList rs) (q : ℕ) (hq : q ≠ rs.length) :
    (Affine.LocalExactness.sectionComplex (internalComplex f i j B b) U).ExactAt q := by
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj
      ((CoefficientLocalPurity.source f i j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU k hUk (coefficients f i) j B q
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U) := IntegralComparison.Finite.FlatCoefficientSections.finite f i U hU
  let : Module.Projective (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U) := IntegralComparison.Finite.FlatCoefficientSections.projective f i U hU
  exact Affine.FiniteProjectivePurity.exactAt U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (CoefficientLocalPurity.source f i j B) (coefficients f i)
    (IntegralComparison.Projective.NegativeResolution.augmentation (coefficients f i) j B)
    (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U) (IntegralComparison.Finite.FlatCoefficientSections.chartIso f i U hU) rs hreg
    (quotientIso i U hU rs hrs)
    (IntegralComparison.Projective.ClosedImmersionPurity.targetTrivialization j b U hU k hUk) q hq

include hU k hUk in
omit [LinearOrder σ] [Flat f] [IsLocallyNoetherian X] in
theorem exactAt_of_unit (hunit : RingHom.ker (i.app U).hom = ⊤) (q : ℕ) :
    (Affine.LocalExactness.sectionComplex (internalComplex f i j B b) U).ExactAt q := by
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj
      ((CoefficientLocalPurity.source f i j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU k hUk (coefficients f i) j B q
  have h1 : (i.app U).hom 1 = 0 := by
    change (1 : Γ(Proj (homogeneousSubmodule σ R), U)) ∈ RingHom.ker (i.app U).hom
    rw [hunit]
    trivial
  let : Subsingleton (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) := subsingleton_of_zero_eq_one (by simpa using h1.symm)
  let : Subsingleton (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U) := Algebra.subsingleton (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) _
  exact Zero.CoefficientPurity.exactAt U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (CoefficientLocalPurity.source f i j B) (coefficients f i)
    (IntegralComparison.Projective.NegativeResolution.augmentation (coefficients f i) j B)
    (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U) (IntegralComparison.Finite.FlatCoefficientSections.chartIso f i U hU) (ModuleCat.isZero_of_subsingleton _) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientLocalPurity
