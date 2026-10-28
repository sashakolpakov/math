import OAI.AlgebraicGeometry.AbelianVariety.CupDimensions
import OAI.AlgebraicTopology.Kunneth.CanonicalCohomology

/-! # Product Spanning -/

namespace OAI.AlgebraicGeometry.AbelianVariety.ProductSpanning.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory
open scoped TensorProduct DirectSum

local instance abelianHomologyFinite (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    FiniteDimensional ℚ
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace A.toOver)).homology n) := by
  let : FiniteDimensional ℚ (A.variety.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety n
  exact AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.finite_homology_of_finite_cohomology
    (Betti.Scheme.schemePointSpace A.toOver) n

theorem abelianProduct_kunneth_generator (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q n : ℕ)
    (h : p + q = n) (a : A.variety.rationalCohomology p) (b : A.variety.rationalCohomology q) :
    AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv (k := ℚ)
      (Betti.Scheme.schemePointSpace A.toOver) (Betti.Scheme.schemePointSpace A.toOver) n
      (DirectSum.lof ℚ _ _ ⟨(p, q), h⟩ (a ⊗ₜ[ℚ] b)) =
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj
      (TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace A.toOver)))
      (ModuleCat.of ℚ ℚ) h
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
        (TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace A.toOver)) p q
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst p a)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd q b)) := by
  subst n
  exact AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv_lof_add
    (Betti.Scheme.schemePointSpace A.toOver) (Betti.Scheme.schemePointSpace A.toOver) p q a b

/-- Actual projection cup products span the cohomology of the point-space product. -/
theorem abelianProduct_cohomology_spanned (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (S : Submodule ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace A.toOver)) n))
    (hcross : ∀ (p q : ℕ) (h : p + q = n)
      (a : A.variety.rationalCohomology p) (b : A.variety.rationalCohomology q),
      AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj
        (TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace A.toOver)))
        (ModuleCat.of ℚ ℚ) h
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
          (TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace A.toOver)) p q
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst p a)
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd q b)) ∈ S) :
    S = ⊤ := by
  classical
  let X := Betti.Scheme.schemePointSpace A.toOver
  let e := AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv (k := ℚ) X X n
  have hs : ∀ x, e x ∈ S := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy => simpa only [map_add] using S.add_mem hx hy
    | of ij x =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simpa only [map_add] using S.add_mem hx hy
      | tmul a b =>
        have he := abelianProduct_kunneth_generator A ij.val.1 ij.val.2 n ij.property a b
        exact he.symm ▸ hcross ij.val.1 ij.val.2 ij.property a b
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨x, rfl⟩ := e.surjective z
  exact hs x

end

end OAI.AlgebraicGeometry.AbelianVariety.ProductSpanning.Constructions.ExteriorCohomology
