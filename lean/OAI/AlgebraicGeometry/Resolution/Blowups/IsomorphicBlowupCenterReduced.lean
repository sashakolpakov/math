import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupChartEtale
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Isomorphic Blowup Center Reduced -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupCenterReduced.Construction

noncomputable section

/-! The exceptional principal ideals in isomorphic smooth-center blowup charts are reduced. -/

open _root_.CategoryTheory

section Maps

variable (k : Type*) {R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

theorem smooth_etale_extended_quotient_hom (φ : R →+* S) (hφ : φ.Etale)
    (hk : ∀ x : k, φ (algebraMap k R x) = algebraMap k S x)
    (I : Ideal R) [Algebra.Smooth k (R ⧸ I)] : Algebra.Smooth k (S ⧸ I.map φ) := by
  let : Algebra R S := φ.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (hk x).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hφ
  exact Blowups.Smooth.TransformedCoordinateHypersurface.Construction.smooth_etale_extended_quotient I

end Maps

universe u

section Smooth

variable (k : Type u) {R : Type u} [CommRing R] [CommRing k] [Algebra k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowupChart_center_quotient_smooth_of_isIso (I : Ideal R)
    [Algebra.Smooth k (R ⧸ I)] [IsIso (ReesGrading.Construction.affineBlowupToSpec I)] (a : I) :
    Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a ⧸ I.map (Blowup.Charts.Construction.blowupChartConstants I a)) :=
  smooth_etale_extended_quotient_hom k (Blowup.Charts.Construction.blowupChartConstants I a)
    (IsomorphicBlowupChartEtale.Construction.blowupChartConstants_etale_of_isIso I a) (fun _ => rfl) I

end Smooth

variable (k : Type u) {R : Type u} [CommRing R] [Field k] [IsAlgClosed k] [Algebra k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The actual exceptional principal ideal is radical because its quotient
is the smooth pullback of the original smooth center. -/
theorem blowupChart_exceptional_span_isRadical (I : Ideal R)
    [Algebra.Smooth k (R ⧸ I)] [IsIso (ReesGrading.Construction.affineBlowupToSpec I)] (a : I) :
    (Ideal.span {Blowup.Charts.Construction.blowupChartConstants I a a.val}).IsRadical := by
  let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a ⧸ I.map (Blowup.Charts.Construction.blowupChartConstants I a)) :=
    blowupChart_center_quotient_smooth_of_isIso k I a
  have hred : IsReduced (Blowup.Charts.Construction.blowupChart I a ⧸ I.map (Blowup.Charts.Construction.blowupChartConstants I a)) := Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k
  have hr := (Ideal.isRadical_iff_quotient_reduced (I.map (Blowup.Charts.Construction.blowupChartConstants I a))).mpr hred
  rwa [ExceptionalIdeal.Construction.blowupChart_extendedIdeal] at hr

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupCenterReduced.Construction
