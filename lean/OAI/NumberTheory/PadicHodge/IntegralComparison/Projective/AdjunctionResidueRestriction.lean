import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientPrincipalRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedQuotientRestriction

/-! # Adjunction Residue Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionResidueRestriction

noncomputable section

/-! The ambient top-form and conormal-residue factors of the original
projective adjunction respect the actual principal-open quotient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] ConormalAdjunction.equivalence
  AmbientAdjunction.ambientIso
  LocalizedResidueRestriction.Conormal.exteriorRestrictionOfEq AffinePrincipal.LineFrame.lineMap

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom]
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U) (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U))

local instance baseAlgebra (W : (IntrinsicOverlap.Intrinsic.space R n).Opens) : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, W) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) W

local instance baseSmooth : Smooth (IntrinsicOverlap.Intrinsic.model R n).hom := SpaceSmooth.smooth

local instance principalTower : IsScalarTower R Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) :=
  IsScalarTower.of_algebraMap_eq (fun a =>
    (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R n)).map (AffinePrincipal.Sections.inclusion U r).op).hom.commutes a).symm)

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] [Smooth X.hom] in
theorem ideal_map : (LocalAdjunction.ideal X f U hU).map
    (algebraMap Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) =
      LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) :=
  IdealSheafPrincipalEquations.ideal_map f.left.ker U hU r

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] [Smooth X.hom] in
theorem quotientHom_eq_native :
    LocalizedResidueRestriction.Conormal.quotientHom (k := R)
        (A := Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (B := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) (LocalAdjunction.ideal X f U hU)
        (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) (ideal_map X f U hU r) =
      Intrinsic.ClosedQuotientRestriction.map R X (IntrinsicOverlap.Intrinsic.model R n) f U (AffinePrincipal.Sections.openSubset U r)
        hU (hU.basicOpen r) (AffinePrincipal.Sections.inclusion U r) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

variable {c g : ℕ}
  (bI : Module.Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (bQ : Module.Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])

def conormalBasis : Module.Basis (Fin c)
    (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
    (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).Cotangent := by
  letI : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
  exact LocalizedConormalBasisTransport.Bases.conormalBasisOfEq
    (A := Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (B := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) r (LocalAdjunction.ideal X f U hU)
    (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) (ideal_map X f U hU r) bI

def quotientBasis : Module.Basis (Fin g)
    (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
    Ω[LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)⁄R] := by
  letI : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
  exact LocalizedConormalBasisTransport.Bases.quotientBasisOfEq (k := R)
    (A := Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (B := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) r (LocalAdjunction.ideal X f U hU)
    (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) (ideal_map X f U hU r) bQ

attribute [local irreducible]
  LocalizedConormalBasisTransport.Bases.conormalBasisOfEq LocalizedConormalBasisTransport.Bases.quotientBasisOfEq
  LocalizedResidueRestriction.Conormal.quotientHom AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap

omit [IsNoetherianRing R] in
theorem residue
    (x : ⋀[LocalAdjunction.quotient X f U hU]^(c + g)
      ((LocalAdjunction.quotient X f U hU) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)] Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R])) :
    letI : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
    letI : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
    letI : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) :=
      Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
    letI : Algebra.Smooth R (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) :=
      Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
    letI : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
    ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r))
        (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
        (conormalBasis X f U hU r bI) (quotientBasis X f U hU r bQ)
      (LocalizedResidueRestriction.Conormal.exteriorRestrictionOfEq (k := R)
        (A := Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (B := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) r
        (LocalAdjunction.ideal X f U hU) (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
        (ideal_map X f U hU r) (c + g) x) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (Intrinsic.ClosedQuotientRestriction.map R X (IntrinsicOverlap.Intrinsic.model R n) f
        U (AffinePrincipal.Sections.openSubset U r) hU (hU.basicOpen r) (AffinePrincipal.Sections.inclusion U r)) g
      (ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, U))
        (LocalAdjunction.ideal X f U hU) bI bQ x) := by
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
  let : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) :=
    Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
  let : Algebra.Smooth R (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) :=
    Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
  let : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
  have hr := LocalizedResidueRestriction.Conormal.residue_restriction (k := R)
    (A := Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (B := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) r (LocalAdjunction.ideal X f U hU) bI bQ
    (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) (ideal_map X f U hU r) x
  have hq := congrArg (fun q : CommAlgCat.of R (LocalAdjunction.quotient X f U hU) ⟶
      CommAlgCat.of R (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) => AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap q g
    (ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, U))
      (LocalAdjunction.ideal X f U hU) bI bQ x)) (quotientHom_eq_native X f U hU r)
  exact hr.trans hq

variable (j i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hc : c + g = n)
  (hIJ : LocalAdjunction.ideal X f U hU ≤ (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).comap
    (algebraMap Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)))

omit [IsNoetherianRing R] [Smooth X.hom] in
theorem ambient_square
    (x : (LocalAdjunction.quotient X f U hU) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
      (AffineOpen.InternalHom.sections U hU).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))) :
    letI : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
    LocalizedResidueRestriction.Conormal.exteriorRestrictionOfEq (k := R)
      (A := Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (B := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) r
      (LocalAdjunction.ideal X f U hU) (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) (ideal_map X f U hU r)
      (c + g) (LocalAdjunction.ambientIso X f j U hU i hUi hc x) =
    LocalAdjunction.ambientIso X f j (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
      (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi) hc
      (AffinePrincipal.LineFrame.lineMap U hU r
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))
        (LocalAdjunction.ideal X f U hU) (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) hIJ x) := by
  let : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
  subst n
  exact AmbientPrincipalRestriction.Adjunction.ambientIso_restriction i U hU hUi r i
    (((IntrinsicOverlap.Intrinsic.space R (c + g)).basicOpen_le r).trans hUi) j
    (LocalAdjunction.ideal X f U hU) (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
    (ideal_map X f U hU r) hIJ x

attribute [local irreducible] LocalAdjunction.ambientIso

omit [IsNoetherianRing R] in
theorem residue_square
    (x : (LocalAdjunction.quotient X f U hU) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
      (AffineOpen.InternalHom.sections U hU).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))) :
    letI : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
    letI : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
    letI : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) :=
      Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
    letI : Algebra.Smooth R (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) :=
      Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
    ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r))
        (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
        (conormalBasis X f U hU r bI) (quotientBasis X f U hU r bQ)
      (LocalAdjunction.ambientIso X f j (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
        (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi) hc
        (AffinePrincipal.LineFrame.lineMap U hU r
          (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))
          (LocalAdjunction.ideal X f U hU) (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) hIJ x)) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (Intrinsic.ClosedQuotientRestriction.map R X (IntrinsicOverlap.Intrinsic.model R n) f
        U (AffinePrincipal.Sections.openSubset U r) hU (hU.basicOpen r) (AffinePrincipal.Sections.inclusion U r)) g
      (ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, U))
        (LocalAdjunction.ideal X f U hU) bI bQ (LocalAdjunction.ambientIso X f j U hU i hUi hc x)) := by
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
  let : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) :=
    Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
  let : Algebra.Smooth R (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) :=
    Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
  let : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
  have hr := residue X f U hU r bI bQ
    (LocalAdjunction.ambientIso X f j U hU i hUi hc x)
  have ha := ambient_square X f U hU r j i hUi hc hIJ x
  have hleft := congrArg
    (ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r))
      (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
      (conormalBasis X f U hU r bI) (quotientBasis X f U hU r bQ)) ha
  exact hleft.symm.trans hr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionResidueRestriction
