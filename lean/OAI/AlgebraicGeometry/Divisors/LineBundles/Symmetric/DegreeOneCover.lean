import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme

/-! # Degree One Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DegreeOneCover.BundleCycles

noncomputable section

/-! The actual projective symmetric spectrum is covered by its charts
at degree-one module generators. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem symmetricGenerator_degree (m : M) :
    SymmetricAlgebra.ι R M m ∈ Grading.BundleCycles.symmetricGrading R M 1 := by
  change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

def symmetricDegreeOneCover : (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M)
    (m := fun _ => 1) (symmetricGenerator_degree R M) (fun _ => by decide)
    (GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal R M).le

theorem symmetricDegreeOneCover_map (m : M) :
    (symmetricDegreeOneCover R M).f m =
      Proj.awayι (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M m)
        (symmetricGenerator_degree R M m) (by decide : 0 < 1) := rfl

instance symmetricDegreeOneCover_isOpenImmersion (m : M) :
    IsOpenImmersion ((symmetricDegreeOneCover R M).f m) :=
  (symmetricDegreeOneCover R M).openCover.map_prop m

theorem symmetricDegreeOneCover_opensRange (m : M) :
    ((symmetricDegreeOneCover R M).f m).opensRange =
      Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M m) :=
  Proj.opensRange_awayι _ _ _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DegreeOneCover.BundleCycles
