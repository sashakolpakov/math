import OAI.AlgebraicGeometry.AbelianVariety.CupDimensions

/-! # Cup Range -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CupRange.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

/-- Appending one factor keeps a product in the canonical exterior-cup image. -/
theorem cup_h1_mem_exteriorCup_range (n : ℕ)
    (a : A.variety.rationalCohomology n) (ha : a ∈ LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A n))
    (b : A.variety.rationalCohomology 1) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1 a b ∈
      LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A (n + 1)) := by
  obtain ⟨x, rfl⟩ := ha
  let L := ((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1).flip b).comp
    (CupMap.Constructions.ExteriorCohomology.exteriorCup A n)
  have hle : (⊤ : Submodule ℚ (⋀[ℚ]^n (A.variety.rationalCohomology 1))) ≤
      (LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A (n + 1))).comap L := by
    rw [← exteriorPower.ιMulti_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    refine ⟨exteriorPower.ιMulti ℚ (n + 1) (Fin.snoc v b), ?_⟩
    change CupMap.Constructions.ExteriorCohomology.exteriorCup A (n + 1) (exteriorPower.ιMulti ℚ (n + 1) (Fin.snoc v b)) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1
        (CupMap.Constructions.ExteriorCohomology.exteriorCup A n (exteriorPower.ιMulti ℚ n v)) b
    simp only [CupMap.Constructions.ExteriorCohomology.exteriorCup_wedge, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalH1Cup, Fin.init_snoc, Fin.snoc_last]
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℚ _))

theorem cup_h1Cup_mem_exteriorCup_range (p : ℕ)
    (a : A.variety.rationalCohomology p) (ha : a ∈ LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A p))
    (q : ℕ) (v : Fin q → A.variety.rationalCohomology 1) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a (A.rationalH1Cup q v) ∈
      LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A (p + q)) := by
  induction q with
  | zero =>
    simpa only [ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalH1Cup, AlgebraicTopology.Products.CupCohomology.singularCohomologyCup,
      AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit, AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_cupUnit] using! ha
  | succ q ih =>
    have hi := cup_h1_mem_exteriorCup_range A (p + q)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a
        (A.rationalH1Cup q (Fin.init v))) (ih (Fin.init v)) (v (Fin.last q))
    have he := AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc
      (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)) a
      (A.rationalH1Cup q (Fin.init v)) (v (Fin.last q))
    have he' : AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) (p + q) 1
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a
          (A.rationalH1Cup q (Fin.init v))) (v (Fin.last q)) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p (q + 1) a
        (A.rationalH1Cup (q + 1) v) := by
      simpa only [AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, LinearMap.id_apply] using! he
    exact he' ▸ hi

/-- The canonical exterior-cup images are closed under actual cup multiplication. -/
theorem cup_mem_exteriorCup_range (p q : ℕ)
    (a : A.variety.rationalCohomology p) (ha : a ∈ LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A p))
    (b : A.variety.rationalCohomology q) (hb : b ∈ LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A q)) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a b ∈
      LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A (p + q)) := by
  obtain ⟨x, rfl⟩ := hb
  let L := (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a).comp
    (CupMap.Constructions.ExteriorCohomology.exteriorCup A q)
  have hle : (⊤ : Submodule ℚ (⋀[ℚ]^q (A.variety.rationalCohomology 1))) ≤
      (LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A (p + q))).comap L := by
    rw [← exteriorPower.ιMulti_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a
      (CupMap.Constructions.ExteriorCohomology.exteriorCup A q (exteriorPower.ιMulti ℚ q v)) ∈
      LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A (p + q))
    rw [CupMap.Constructions.ExteriorCohomology.exteriorCup_wedge]
    exact cup_h1Cup_mem_exteriorCup_range A p a ha q v
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℚ _))

end

end OAI.AlgebraicGeometry.AbelianVariety.CupRange.Constructions.ExteriorCohomology
