import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductGeometry
import OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Product Dimensions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductDimensions

noncomputable section

/-!
The actual Künneth theorem gives the dimension of H¹ of a finite product.
Together with the already proved splitting, this proves bijectivity of the
canonical sum of projection pullbacks. Connectedness and finiteness are
ordinary geometric/topological properties, not comparison assumptions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped DirectSum TensorProduct

open OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition

def bettiIso {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (e : X ≅ Y) (n : ℕ) :
    Product.bettiQ Y n ≃ₗ[ℚ] Product.bettiQ X n :=
  ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) n).mapIso e.op).toLinearEquiv

theorem betti_finite_of_iso {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (e : X ≅ Y) (n : ℕ)
    [FiniteDimensional ℚ (Product.bettiQ Y n)] : FiniteDimensional ℚ (Product.bettiQ X n) :=
  Module.Finite.of_surjective (bettiIso e n).toLinearMap (bettiIso e n).surjective

def h0HomologyEquiv (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] :
    (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X)).homology 0 ≃ₗ[ℚ] ℚ := by
  let : PathConnectedSpace (Betti.Scheme.schemePointSpace X) :=
    inferInstanceAs (PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  exact (asIso ((Betti.Scheme.schemePointSpace X).singularHomology₀ε
    (C := ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ))).toLinearEquiv

theorem betti_zero_finite (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] : FiniteDimensional ℚ (Product.bettiQ X 0) := by
  let : FiniteDimensional ℚ
      ((OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X)).homology 0) :=
    Module.Finite.of_injective (h0HomologyEquiv X).toLinearMap (h0HomologyEquiv X).injective
  exact Module.Finite.of_injective
    (OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (Betti.Scheme.schemePointSpace X) 0).toLinearMap
    (OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (Betti.Scheme.schemePointSpace X) 0).injective

theorem betti_zero_finrank (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] : Module.finrank ℚ (Product.bettiQ X 0) = 1 := by
  let : FiniteDimensional ℚ
      ((OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X)).homology 0) :=
    Module.Finite.of_injective (h0HomologyEquiv X).toLinearMap (h0HomologyEquiv X).injective
  rw [(OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (Betti.Scheme.schemePointSpace X) 0).finrank_eq,
    Subspace.dual_finrank_eq, (h0HomologyEquiv X).finrank_eq]
  exact Module.finrank_self ℚ

def tensorKunnethEquiv (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [∀ n, FiniteDimensional ℚ (Product.bettiQ X n)]
    [∀ n, FiniteDimensional ℚ (Product.bettiQ Y n)] (n : ℕ) :
    OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.CohomologySum (k := ℚ) (Betti.Scheme.schemePointSpace X) (Betti.Scheme.schemePointSpace Y) n ≃ₗ[ℚ]
      Product.bettiQ (X ⊗ Y) n := by
  let : ∀ m, FiniteDimensional ℚ
      ((OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X)).homology m) := fun m =>
    OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.finite_homology_of_finite_cohomology (Betti.Scheme.schemePointSpace X) m
  let : ∀ m, FiniteDimensional ℚ
      ((OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace Y)).homology m) := fun m =>
    OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.finite_homology_of_finite_cohomology (Betti.Scheme.schemePointSpace Y) m
  exact (OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologyKunnethEquiv (Betti.Scheme.schemePointSpace X) (Betti.Scheme.schemePointSpace Y) n).trans
    (((OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of ℚ ℚ) n).mapIso
      (TopCat.isoOfHomeo (AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology.schemePointProductHomeomorph X Y)).op).toLinearEquiv)

theorem tensorBetti_finite (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [∀ n, FiniteDimensional ℚ (Product.bettiQ X n)]
    [∀ n, FiniteDimensional ℚ (Product.bettiQ Y n)] (n : ℕ) :
    FiniteDimensional ℚ (Product.bettiQ (X ⊗ Y) n) :=
  Module.Finite.of_surjective (tensorKunnethEquiv X Y n).toLinearMap
    (tensorKunnethEquiv X Y n).surjective

theorem tensorBetti_one_finrank (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [∀ n, FiniteDimensional ℚ (Product.bettiQ X n)]
    [∀ n, FiniteDimensional ℚ (Product.bettiQ Y n)]
    [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] :
    Module.finrank ℚ (Product.bettiQ (X ⊗ Y) 1) =
      Module.finrank ℚ (Product.bettiQ X 1) + Module.finrank ℚ (Product.bettiQ Y 1) := by
  rw [← (tensorKunnethEquiv X Y 1).finrank_eq]
  unfold OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.CohomologySum
  rw [Module.finrank_directSum]
  simp only [Module.finrank_tensorProduct]
  rw [← Equiv.sum_comp (OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.degreePairsEquiv 1)]
  simp [OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.degreePairsEquiv, Fin.sum_univ_succ]
  change Module.finrank ℚ (Product.bettiQ X 0) * Module.finrank ℚ (Product.bettiQ Y 1) +
    Module.finrank ℚ (Product.bettiQ X 1) * Module.finrank ℚ (Product.bettiQ Y 0) = _
  rw [betti_zero_finrank, betti_zero_finrank]
  omega

theorem unitBetti_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (Product.bettiQ (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)) n) := by
  let : Subsingleton (Betti.Scheme.schemePointSpace (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase))) :=
    inferInstanceAs (Subsingleton (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)))
  exact ModuleCat.subsingleton_of_isZero
    (OAI.AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_totallyDisconnected (ModuleCat.of ℚ ℚ)
      (Betti.Scheme.schemePointSpace (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase))) n hn)

theorem unitBetti_finite (n : ℕ) : FiniteDimensional ℚ (Product.bettiQ (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)) n) := by
  by_cases hn : n = 0
  · subst n
    let : PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase))) :=
      ProductGeometry.unitPoints_pathConnected
    exact betti_zero_finite _
  · let : Subsingleton (Product.bettiQ (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)) n) := unitBetti_subsingleton n hn
    infer_instance

theorem piBetti_finite (n : ℕ) (X : Fin n → Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [∀ i m, FiniteDimensional ℚ (Product.bettiQ (X i) m)] :
    ∀ m, FiniteDimensional ℚ (Product.bettiQ (∏ᶜ X) m) := by
  induction n with
  | zero =>
    intro m
    let : FiniteDimensional ℚ (Product.bettiQ (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)) m) := unitBetti_finite m
    exact betti_finite_of_iso (ProductGeometry.piZeroIso X) m
  | succ n ih =>
    let : ∀ m, FiniteDimensional ℚ (Product.bettiQ (∏ᶜ (fun i : Fin n => X i.succ)) m) :=
      ih (fun i => X i.succ)
    intro m
    let : FiniteDimensional ℚ (Product.bettiQ (X 0 ⊗ ∏ᶜ (fun i : Fin n => X i.succ)) m) :=
      tensorBetti_finite _ _ m
    exact betti_finite_of_iso (ProductGeometry.piSuccIso X) m

theorem piBetti_one_finrank (n : ℕ) (X : Fin n → Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [∀ i m, FiniteDimensional ℚ (Product.bettiQ (X i) m)]
    [∀ i, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X i))] :
    Module.finrank ℚ (Product.bettiQ (∏ᶜ X) 1) =
      ∑ i, Module.finrank ℚ (Product.bettiQ (X i) 1) := by
  induction n with
  | zero =>
    let : Subsingleton (Product.bettiQ (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)) 1) := unitBetti_subsingleton 1 (by decide)
    rw [← (bettiIso (ProductGeometry.piZeroIso X) 1).finrank_eq]
    simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    let : ∀ m, FiniteDimensional ℚ (Product.bettiQ (∏ᶜ (fun i : Fin n => X i.succ)) m) :=
      piBetti_finite n (fun i => X i.succ)
    let : PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (∏ᶜ (fun i : Fin n => X i.succ))) :=
      ProductGeometry.piPoints_pathConnected n (fun i => X i.succ)
    rw [← (bettiIso (ProductGeometry.piSuccIso X) 1).finrank_eq, tensorBetti_one_finrank,
      ih (fun i => X i.succ), Fin.sum_univ_succ]

/-- The canonical degree-one projection-sum map is a genuine isomorphism. -/
theorem ProductBetti.projectionSum_bijective {r : ℕ}
    (A : Fin r → CommGrp (Over Foundations.Scheme.ProjectiveSpace.complexBase))
    [∀ i m, FiniteDimensional ℚ (Product.bettiQ (A i).X m)]
    [∀ i, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A i).X)] :
    Function.Bijective (Product.ProductBetti.projectionSum A 1) := by
  let : FiniteDimensional ℚ (Product.bettiQ (Product.ProductBetti.scheme A) 1) :=
    piBetti_finite r (fun i => (A i).X) 1
  have hdim : Module.finrank ℚ (∀ i, Product.bettiQ (A i).X 1) =
      Module.finrank ℚ (Product.bettiQ (Product.ProductBetti.scheme A) 1) := by
    rw [Module.finrank_pi_fintype, piBetti_one_finrank]
  have hinj := Product.ProductBetti.projectionSum_injective A 1 (by decide)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductDimensions
