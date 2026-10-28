import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointQuotientSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSerre
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SupportedSurvivor

/-! # Survivor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor

noncomputable section

/-! The survivor of the original fixed point resolution is the
direct image of the point's genuine degree-zero form sheaf. The
coefficient change uses the actual common negative resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

def pointModel (R : Type u) [CommRing R] : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)

instance point_smooth : SmoothOfRelativeDimension 0 (pointModel R).hom := by
  change SmoothOfRelativeDimension 0 (𝟙 (Spec (CommRingCat.of R)))
  infer_instance

instance point_proper : IsProper (pointModel R).hom := by
  change IsProper (𝟙 (Spec (CommRingCat.of R)))
  infer_instance

variable {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion i] (s : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s]
  (hs : s ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n + 2 ≤ B)

def pointEmbedding : pointModel R ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1) :=
  Over.homMk (s ≫ i) (by
    change (s ≫ i) ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = 𝟙 _
    simpa only [Category.assoc] using hs)

instance point_embedding_closed : IsClosedImmersion (pointEmbedding i s hs).left :=
  inferInstanceAs (IsClosedImmersion (s ≫ i))

abbrev coefficient := Projective.SectionClass.point i s
abbrev chart (R : Type u) : Fin (n+2) :=
  let _ := R
  NegativeTwistResidueNaturality.topChart.{u} (n+1) (Fintype.card_fin (n+2))

local instance coefficient_qc : (coefficient i s).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent s i
local instance coefficient_finite : (coefficient i s).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType s i

abbrev complex := Projective.NegativeResolution.complex (coefficient i s) (chart (R := R)) B
abbrev dual := (ProjectiveRefinement.DualMap.dualFunctor (R := R) (chart (R := R)) (n+2)).obj
  (op (complex i s B))
abbrev survivor := (dual i s B).homology (n+1)

def closedIso (q : ℕ) : (dual i s B).homology q ≅
    ((ProjectiveRefinement.DualMap.dualFunctor (R := R) (chart (R := R)) (n+2)).obj
      (op (Projective.NegativeResolution.complex
        (Projective.ClosedImmersionPurity.directImage (s ≫ i)) (chart (R := R)) B))).homology q :=
  ProjectiveRefinement.DualIso.iso
    (Projective.ClosedImmersionPurity.directImage (s ≫ i)) (coefficient i s)
    (chart (R := R)) B (n+2) hB (Closed.PointQuotientSquare.pointIso s i).symm q

abbrev forms := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (pointModel R) 0

def adjunctionIso : survivor i s B ≅ (Scheme.Modules.pushforward (s ≫ i)).obj (forms (R := R)) := by
  letI : Smooth (pointModel R).hom := SmoothOfRelativeDimension.smooth 0 _
  exact closedIso i s B hB (n+1) ≪≫
    Projective.AdjunctionGlobal.iso (pointModel R) (pointEmbedding i s hs) 0
      (chart (R := R)) B hB (Nat.zero_le _)

include hs hB in
theorem exactAt (q : ℕ) (hq : q ≠ n+1) : (dual i s B).ExactAt q := by
  let : SmoothOfRelativeDimension 0 ((s ≫ i) ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
    have he : (s ≫ i) ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = 𝟙 _ := by simpa only [Category.assoc] using hs
    rw [he]
    infer_instance
  have h := IntegralComparison.Smooth.ProjectiveSerre.exactAt (s ≫ i) B n (Fintype.card_fin (n+2)) hB 0 q
    (by simpa only [Nat.sub_zero] using hq)
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  apply (closedIso i s B hB q).isZero_iff.mpr
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h

abbrev sections_zero := Closed.SupportedSurvivor.sections_zero (s ≫ i)
  (forms (R := R)) (survivor i s B) (adjunctionIso i s hs B hB)

abbrev terms_zero (c q : ℕ) := Closed.SupportedSurvivor.terms_zero (s ≫ i)
  (forms (R := R)) (survivor i s B) (adjunctionIso i s hs B hB) c q

abbrev lift (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) :=
  Closed.SupportedSurvivor.lift (s ≫ i) (forms (R := R)) (survivor i s B)
    (adjunctionIso i s hs B hB) U (n+1)

abbrev homology_extension (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens)
    (hU : ⊤ ≤ (s ≫ i) ⁻¹ᵁ U) (q : ℕ) :=
  Closed.SupportedSurvivor.homology_extension (s ≫ i) (forms (R := R)) (survivor i s B)
    (adjunctionIso i s hs B hB) U hU (n+1) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
