import OAI.AlgebraicGeometry.AbelianVariety.CupGeneration

/-! # Cup Spanning -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupSpanning

noncomputable section

/-! Actual rational degree-two classes are spanned by degree-one cups. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.AbelianVariety.CupGeneration.Constructions.ExteriorCohomology

theorem abelianH2_cup_spanned (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (S : Submodule ℚ (A.variety.rationalCohomology 2))
    (hc : ∀ a b : A.variety.rationalCohomology 1,
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1 a b ∈ S) : S = ⊤ := by
  have he : Submodule.comap (AbelianVariety.CupMap.Constructions.ExteriorCohomology.exteriorCup A 2) S = ⊤ := by
    apply top_unique
    rw [← exteriorPower.ιMulti_span ℚ 2 (A.variety.rationalCohomology 1)]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change AbelianVariety.CupMap.Constructions.ExteriorCohomology.exteriorCup A 2 (exteriorPower.ιMulti ℚ 2 v) ∈ S
    rw [AbelianVariety.CupMap.Constructions.ExteriorCohomology.exteriorCup_wedge]
    have hu := AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit_cup (R := ℚ)
      (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)) (v 0)
    have hv : A.rationalH1Cup 2 v =
        AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1 (v 0) (v 1) := by
      simpa [ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalH1Cup, AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, Fin.init] using
        congrArg (fun x => AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1 x (v 1)) hu
    rw [hv]
    exact hc _ _
  apply top_unique
  intro c _
  obtain ⟨z, rfl⟩ := AbelianVariety.CupGeneration.Constructions.ExteriorCohomology.exteriorCup_surjective A 2 c
  exact (show z ∈ Submodule.comap (AbelianVariety.CupMap.Constructions.ExteriorCohomology.exteriorCup A 2) S from he.symm ▸ Submodule.mem_top)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupSpanning
