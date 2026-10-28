import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionDualPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ImmersionQuotientSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageType

/-! # Closed Immersion Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ClosedImmersionPurity

noncomputable section

/-! The genuine dual negative-twist resolution of a closed subscheme is
locally pure on affine coordinate subopens with regular defining equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]

abbrev directImage := Closed.ImmersionQuotientSections.directImage f

instance directImage_quasicoherent : (directImage f).IsQuasicoherent := by
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)

instance directImage_finiteType : (directImage f).IsFiniteType := by
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsFiniteType := by
    have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsFinitePresentation :=
      AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_finitePresentation AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hq.isFinite_presentation i).isFiniteType_generators
  exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageType.finite_directImage_finiteType f (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)

variable (j : σ) (B b : ℕ)

abbrev source := NegativeResolution.complex (directImage f) j B

instance source_quasicoherent (n : ℕ) : ((ClosedImmersionPurity.source f j B).X n).IsQuasicoherent :=
  inferInstanceAs ((NegativeResolution.presentation
    (NegativeResolution.state (directImage f) j B n).module j B).source.IsQuasicoherent)

def internalComplex := SchemeInternalHom.complex (.up ℕ)
  (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (ClosedImmersionPurity.source f j B).op

variable (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

def sectionComplex :=
  (((Affine.ModuleExactSections.sections U ⋙ forget₂ _ AddCommGrpCat).mapHomologicalComplex
    (.up ℕ)).obj (internalComplex f j B b))

variable (rs : List Γ(Proj (homogeneousSubmodule σ R), U))
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U) rs)
  (hrs : RingHom.ker (f.app U).hom = Ideal.ofList rs)

def targetTrivialization :
    (AffineOpen.InternalHom.sections U hU).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) ≅
      ModuleCat.of Γ(Proj (homogeneousSubmodule σ R), U) Γ(Proj (homogeneousSubmodule σ R), U) :=
  Affine.ProjectiveResolutionTerms.trivialSectionIso U hU _
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hUi
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) i j b))

def purityIso :
    (sectionComplex f j B b U).homology rs.length ≅
      (forget₂ (ModuleCat Γ(Proj (homogeneousSubmodule σ R), U)) AddCommGrpCat).obj
        (ProjectiveResolution.DualPurity.quotient Γ(Proj (homogeneousSubmodule σ R), U) rs) := by
  let (n : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((ClosedImmersionPurity.source f j B).X n)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (directImage f) j B n
  exact Affine.ResolutionDualPurity.purityIso U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (ClosedImmersionPurity.source f j B) (directImage f)
    (NegativeResolution.augmentation (directImage f) j B) rs hreg
    (Closed.ImmersionQuotientSections.chartQuotientIso f U hU rs hrs)
    (targetTrivialization j b U hU i hUi)

include hU i hUi hreg hrs in
omit [LinearOrder σ] in
theorem exactAt (n : ℕ) (hn : n ≠ rs.length) : (sectionComplex f j B b U).ExactAt n := by
  let (m : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((ClosedImmersionPurity.source f j B).X m)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (directImage f) j B m
  exact Affine.ResolutionDualPurity.exactAt U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (ClosedImmersionPurity.source f j B) (directImage f)
    (NegativeResolution.augmentation (directImage f) j B) rs hreg
    (Closed.ImmersionQuotientSections.chartQuotientIso f U hU rs hrs)
    (targetTrivialization j b U hU i hUi) n hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ClosedImmersionPurity
