import OAI.AlgebraicGeometry.ComplexMultiplication.GeometricMonomialReduction
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCupUnit
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Multilinear.Basis
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPullback

/-! # Iterated Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IteratedCup.CM.Construction

noncomputable section

/-! Iterated actual H1 cup products as multilinear maps. The complex
exterior comparison is identified with this product on every tuple. -/

open _root_.CategoryTheory
open scoped TensorProduct Classical

def h1Cup (R : Type) [CommRing R] (X : TopCat.{0}) :
    (n : ℕ) → MultilinearMap R
      (fun _ : Fin n => AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1)
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n)
  | 0 => MultilinearMap.constOfIsEmpty R _ (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit X)
  | n + 1 => MultilinearMap.uncurryRight
      ((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X n 1).compMultilinearMap (h1Cup R X n))

theorem h1Cup_succ (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (v : Fin (n + 1) → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    Construction.h1Cup R X (n + 1) v = AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X n 1
      (Construction.h1Cup R X n (Fin.init v)) (v (Fin.last n)) := rfl

theorem h1Cup_rational (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin n → A.variety.rationalCohomology 1) :
    Construction.h1Cup ℚ (Betti.Scheme.schemePointSpace A.toOver) n v = A.rationalH1Cup n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup _ n 1 (Construction.h1Cup ℚ _ n (Fin.init v)) _ = _
    rw [ih]
    rfl

theorem h1Cup_rationalToComplex (X : TopCat.{0}) (n : ℕ)
    (v : Fin n → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n (Construction.h1Cup ℚ X n v) =
      Construction.h1Cup ℂ X n (fun i => AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X 1 (v i)) := by
  induction n with
  | zero => exact ComplexMultiplication.HodgeComparison.RationalCupUnit.CM.Construction.rationalToComplexCohomology_unit X
  | succ n ih =>
    change AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X (n + 1)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X n 1 (Construction.h1Cup ℚ X n (Fin.init v)) (v (Fin.last n))) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X n 1
        (Construction.h1Cup ℂ X n (fun i => AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X 1 (v i.castSucc)))
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X 1 (v (Fin.last n)))
    erw [ComplexMultiplication.HodgeComparison.RationalCup.CM.Construction.rationalToComplexCohomology_cup, ih]
    rfl

theorem complexMap_exteriorProduct {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
    (C : ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H) (n : ℕ)
    (v : Fin n → ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    C.complexMap n ((ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm
      (exteriorPower.ιMulti ℂ n v)) =
    Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) n
      (fun i => ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1 (v i)) := by
  let F := (C.complexMap n).compMultilinearMap
    ((ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm.toLinearMap.compMultilinearMap
      (exteriorPower.ιMulti ℂ n).toMultilinearMap)
  let G := (Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) n).compLinearMap
    (fun _ => ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1)
  have hFG : F = G := by
    apply Module.Basis.ext_multilinear
      (fun _ => (Module.Free.chooseBasis ℚ (A.variety.rationalCohomology 1)).baseChange ℂ)
    intro w
    simp only [F, G, LinearMap.compMultilinearMap_apply,
      MultilinearMap.compLinearMap_apply, AlternatingMap.coe_multilinearMap,
      Module.Basis.baseChange_apply]
    have hi := ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChange_tmul_ιMulti ℂ (A.variety.rationalCohomology 1) n
      1 (fun i => Module.Free.chooseBasis ℚ (A.variety.rationalCohomology 1) (w i))
    rw [one_smul] at hi
    change ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n _ = _ at hi
    rw [← hi]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    simp only [ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison.complexMap, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, LinearEquiv.coe_coe, C.wedge,
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
    rw [← h1Cup_rational, h1Cup_rationalToComplex]
  exact MultilinearMap.congr_fun hFG v

local instance {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
    (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H) : LinearOrder D.EmbeddingIndex := linearOrderOfSTO WellOrderingRel

theorem complexMap_embeddingMonomial {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
    (C : ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H) (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H) (n : ℕ)
    (s : D.ExteriorIndex n) :
    C.complexMap n (D.complexExteriorEmbeddingBasis n s) =
      Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) n
        (fun i => ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
          (D.embeddingBasis (D.exteriorEmbeddingTuple n s i))) := by
  have hb : D.complexExteriorEmbeddingBasis n s =
      (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm
        (exteriorPower.ιMulti ℂ n
          (fun i => D.embeddingBasis (D.exteriorEmbeddingTuple n s i))) := by
    rw [ComplexMultiplication.Decomposition.CM.CMDecomposition.complexExteriorEmbeddingBasis, Module.Basis.map_apply,
      exteriorPower.basis_apply]
    unfold exteriorPower.ιMulti_family ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorEmbeddingTuple
    apply congrArg (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm
    apply congrArg (exteriorPower.ιMulti ℂ n)
    funext i
    simp only [Function.comp_apply]
  rw [hb]
  exact complexMap_exteriorProduct C n
    (fun i => D.embeddingBasis (D.exteriorEmbeddingTuple n s i))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IteratedCup.CM.Construction
