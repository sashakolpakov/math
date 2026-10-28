import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth Stalk Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.SmoothStalkCriterion

noncomputable section

/-! Algebraic smoothness at a prime gives formal smoothness of the corresponding scheme stalk map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem spec_stalk_formallySmooth_of_isSmoothAt
    {C A : Type u} [CommRing C] [CommRing A] [Algebra C A]
    (q : PrimeSpectrum A) [Algebra.IsSmoothAt C q.asIdeal] :
    ((Spec.map (CommRingCat.ofHom (algebraMap C A))).stalkMap q).hom.FormallySmooth := by
  let p := q.comap (algebraMap C A)
  have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have : Algebra.FormallySmooth (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (Algebra.FormallySmooth.iff_restrictScalars (R := C)
      (A := Localization.AtPrime p.asIdeal) (B := Localization.AtPrime q.asIdeal)).mp inferInstance
  apply (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap C A)) q)).mpr
  exact RingHom.formallySmooth_algebraMap.mpr
    (inferInstanceAs (Algebra.FormallySmooth (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.SmoothStalkCriterion
