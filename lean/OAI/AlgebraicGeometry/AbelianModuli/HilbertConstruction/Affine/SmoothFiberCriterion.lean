import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.SmoothStalkCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SmoothFiberAlgebra

/-! # Smooth Fiber Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SmoothFiberCriterion

noncomputable section

/-! A smooth fiber of a flat finitely presented affine family lies in the smooth locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem spec_stalk_formallySmooth_of_smooth_fiber
    {C A : Type u} [CommRing C] [CommRing A] [Algebra C A]
    [Algebra.FinitePresentation C A] [Module.Flat C A] (q : PrimeSpectrum A)
    [Smooth ((Spec.map (CommRingCat.ofHom (algebraMap C A))).fiberToSpecResidueField
      (q.comap (algebraMap C A)))] :
    ((Spec.map (CommRingCat.ofHom (algebraMap C A))).stalkMap q).hom.FormallySmooth := by
  let p := q.comap (algebraMap C A)
  have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber A) := SmoothFiberAlgebra.algebraFiber_smooth_of_specFiber p
  have : Algebra.IsSmoothAt C q.asIdeal := Algebra.IsSmoothAt.of_formallySmooth_fiber p.asIdeal q.asIdeal
  exact HilbertConstruction.Spec.SmoothStalkCriterion.spec_stalk_formallySmooth_of_isSmoothAt q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SmoothFiberCriterion
