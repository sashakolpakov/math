import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Isomorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ClosedImmersionPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomCoherence

/-! # Local Dual Line -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalDualLine

noncomputable section

/-! On an affine coordinate subopen with regular defining equations,
the surviving dual cohomology is the actual rank-one module on the
closed subscheme. All isomorphisms retain the ambient module action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ClosedImmersionPurity

variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
  (j : σ) (B b : ℕ) (hb : b ≤ B)

include hb in
omit [LinearOrder σ] in
theorem term_quasicoherent (q : ℕ) : ((ClosedImmersionPurity.internalComplex f j B b).X q).IsQuasicoherent :=
  InternalHomCoherence.term (ClosedImmersionPurity.directImage f) j B b hb q

include hb in
omit [LinearOrder σ] in
theorem homology_quasicoherent (q : ℕ) : ((ClosedImmersionPurity.internalComplex f j B b).homology q).IsQuasicoherent := by
  let (n : ℕ) : ((ClosedImmersionPurity.internalComplex f j B b).X n).IsQuasicoherent :=
    term_quasicoherent f j B b hb n
  exact QuasicoherentTruncation.cohomology (ClosedImmersionPurity.internalComplex f j B b) q

variable (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (rs : List Γ(Proj (homogeneousSubmodule σ R), U))
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U) rs)
  (hrs : RingHom.ker (f.app U).hom = Ideal.ofList rs)

def sectionIso :
    (Affine.ModuleExactSections.sections U).obj ((ClosedImmersionPurity.internalComplex f j B b).homology rs.length) ≅
      (Affine.ModuleExactSections.sections U).obj (ClosedImmersionPurity.directImage f) := by
  let (n : ℕ) : ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (ClosedImmersionPurity.source f j B)).X n).IsQuasicoherent :=
    term_quasicoherent f j B b hb n
  let (n : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((ClosedImmersionPurity.source f j B).X n)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (ClosedImmersionPurity.directImage f) j B n
  exact Affine.LinearResolutionPurity.cohomologySheafIso U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) (ClosedImmersionPurity.source f j B) (ClosedImmersionPurity.directImage f)
    (NegativeResolution.augmentation (ClosedImmersionPurity.directImage f) j B) rs hreg
    (Closed.ImmersionQuotientSections.chartQuotientIso f U hU rs hrs)
    (ClosedImmersionPurity.targetTrivialization j b U hU i hUi) ≪≫
      Closed.ImmersionQuotientSections.listQuotientIso f U hU rs hrs

def openIso : ((ClosedImmersionPurity.internalComplex f j B b).homology rs.length).restrict U.ι ≅
    (ClosedImmersionPurity.directImage f).restrict U.ι := by
  letI := homology_quasicoherent f j B b hb rs.length
  exact AffineSection.Isomorphism.openIso U hU _ _
    (sectionIso f j B b hb U hU i hUi rs hreg hrs)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalDualLine
