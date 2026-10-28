import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Smooth.Basic

/-! # Principal Smooth Localization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrincipalSmoothLocalization.Constructions

noncomputable section

/-!
# DegreeTwo: smoothness of the actual localized principal hypersurface

The quotient-localization equivalence identifies the hypersurface on an
ambient principal open with the corresponding principal open of the quotient.
-/

/-- A smooth principal open of the quotient is the smooth principal
hypersurface in the corresponding ambient localization. -/
theorem principal_quotient_localization_smooth (K R : Type*) [CommRing K] [CommRing R]
    [Algebra K R] (p b : R)
    [Algebra.Smooth K (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))] :
    Algebra.Smooth K (Localization.Away b ⧸
      Ideal.span ({algebraMap R (Localization.Away b) p} : Set (Localization.Away b))) := by
  let I := Ideal.span ({p} : Set R)
  let A := Localization.Away b
  let B := A ⧸ I.map (algebraMap R A)
  let q := Ideal.Quotient.mk I b
  have hM : Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers b) = Submonoid.powers q :=
    Submonoid.map_powers (Ideal.Quotient.mk I) b
  let : IsLocalization (Submonoid.powers q) B := by
    rw [← hM]
    infer_instance
  let e := IsLocalization.algEquiv (Submonoid.powers q) (Localization.Away q) B
  let : IsScalarTower K (R ⧸ I) B := IsScalarTower.of_algebraMap_eq (fun k => by
    change Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap K A k) =
      Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A (algebraMap K R k))
    rw [IsScalarTower.algebraMap_apply K R A])
  have hB : Algebra.Smooth K B := Algebra.Smooth.of_equiv (e.restrictScalars K)
  change Algebra.Smooth K (A ⧸ Ideal.span {algebraMap R A p})
  have hI : I.map (algebraMap R A) = Ideal.span {algebraMap R A p} := by
    change (Ideal.span {p}).map (algebraMap R A) = _
    rw [Ideal.map_span, Set.image_singleton]
  rw [← hI]
  exact hB

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrincipalSmoothLocalization.Constructions
