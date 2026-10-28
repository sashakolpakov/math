import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.ComplexCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.DiskProductSphereGenerator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.FillingCycle
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact

/-! # Positive Complex Sphere -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PositiveComplexSphere

noncomputable section

section

/-!
# ChernClass: explicit fillings represent the original complex local generator

Transport the actual Euclidean orthant filling through the inverse original
complex coordinates. Its native relative boundary has the already computed
positive sphere coordinate, so the class is the original integral generator.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def positiveComplexOrthantPuncturedCycle (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ)))) (2 * p + 1) :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Positive.ComplexCoordinates.positiveEuclideanToComplexPunctured p))
    (2 * p + 1) (DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p))

def positiveComplexOrthantFilling (p : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin (p + 1) → ℂ))).X (2 * p + 2) :=
  (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Positive.ComplexCoordinates.positiveEuclideanToComplex p)).f (2 * p + 2)
    (DiskProductSphereGenerator.euclideanOrthantFilling (2 * p))

theorem positiveComplexOrthantFilling_boundary (p : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin (p + 1) → ℂ))).d (2 * p + 2) (2 * p + 1)
      (positiveComplexOrthantFilling p) =
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)).f (2 * p + 1)
        (positiveComplexOrthantPuncturedCycle p).val := by
  have h := ConcreteCategory.congr_hom
    ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Positive.ComplexCoordinates.positiveEuclideanToComplex p)).comm (2 * p + 2) (2 * p + 1))
    (DiskProductSphereGenerator.euclideanOrthantFilling (2 * p))
  change _ = (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Positive.ComplexCoordinates.positiveEuclideanToComplex p)).f (2 * p + 1)
    ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (EuclideanSpace ℝ (Fin (2 * p + 2))))).d
      (2 * p + 2) (2 * p + 1) (DiskProductSphereGenerator.euclideanOrthantFilling (2 * p))) at h
  rw [DiskProductSphereGenerator.euclideanOrthantFilling_boundary] at h
  refine h.trans ?_
  have hm := congrArg (fun f => f.f (2 * p + 1))
    (congrArg CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Positive.ComplexCoordinates.positiveEuclideanToComplex_inclusion p))
  rw [CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_comp, CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm (DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p)).val

def positiveComplexOrthantRelativeCycle (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)) (2 * p + 2) :=
  Relative.FillingCycle.relativeFillingCycle ℤ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) (2 * p + 1)
    (positiveComplexOrthantFilling p) (positiveComplexOrthantPuncturedCycle p)
    (positiveComplexOrthantFilling_boundary p)

def positiveComplexOrthantRelativeClass (p : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 (2 * p + 2) :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (2 * p + 2) (positiveComplexOrthantRelativeCycle p)

theorem positiveComplexOrthantRelativeClass_boundary (p : ℕ) :
    CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) (2 * p + 1)
      (positiveComplexOrthantRelativeClass p) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ))))
        (2 * p + 1) (positiveComplexOrthantPuncturedCycle p) :=
  Relative.FillingCycle.relativeFillingCycle_boundary ℤ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) (2 * p + 1)
    (positiveComplexOrthantFilling p) (positiveComplexOrthantPuncturedCycle p)
    (positiveComplexOrthantFilling_boundary p)

theorem positiveComplexOrthantPuncturedCycle_coordinates (p : ℕ) :
    CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
      (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
        (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩) (2 * p + 1)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ))))
        (2 * p + 1) (positiveComplexOrthantPuncturedCycle p)) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains
        (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p + 2))))))
        (2 * p + 1) (DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p)) := by
  have hc := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Positive.ComplexCoordinates.positiveEuclideanToComplexPunctured p))
    (2 * p + 1) (DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p))
  change _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ))))
    (2 * p + 1) (positiveComplexOrthantPuncturedCycle p) at hc
  rw [← hc]
  have hm : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (Positive.ComplexCoordinates.positiveEuclideanToComplexPunctured p) (2 * p + 1) ≫
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
        (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
          (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩) (2 * p + 1) = 𝟙 _ := by
    simp only [CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap, ← HomologicalComplex.homologyMap_comp,
      ← CategoryTheory.Functor.map_comp, Positive.ComplexCoordinates.positiveEuclideanToComplexPunctured_coordinates]
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  exact ConcreteCategory.congr_hom hm
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p + 2))))))
      (2 * p + 1) (DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p)))

theorem positiveComplexOrthantRelativeClass_sphere (p : ℕ) :
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1) (Nat.succ_ne_zero _)).hom
      (positiveComplexOrthantRelativeClass p) = OrthantSphereCycle.orientedOrthantSphereClass (2 * p + 1) := by
  rw [Positive.ComplexCoordinates.positiveComplexNormalLocalStandardSphereIso_ordered]
  change CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
    (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p + 2))))) (2 * p + 1)
    (CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
      (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
        (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩) (2 * p + 1)
      (CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) (2 * p + 1)
        (positiveComplexOrthantRelativeClass p))) = _
  rw [positiveComplexOrthantRelativeClass_boundary, positiveComplexOrthantPuncturedCycle_coordinates]
  have hc := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
      (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereInclusion (EuclideanSpace ℝ (Fin (2 * p + 2))))))
    (2 * p + 1) (OrthantSphereCycle.orientedOrthantSphereCycle (2 * p + 1))
  change _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains
    (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p + 2))))))
      (2 * p + 1) (DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p)) at hc
  rw [← hc]
  exact (CycleClass.Geometric.NormalSphereHomology.Cycles.normalSphereIntegralHomologyIso (EuclideanSpace ℝ (Fin (2 * p + 2)))
    (2 * p + 1)).inv_hom_id_apply (OrthantSphereCycle.orientedOrthantSphereClass (2 * p + 1))

theorem positiveComplexOrthantRelativeClass_eq_originalGenerator (p : ℕ) :
    positiveComplexOrthantRelativeClass p = (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).inv 1 := by
  apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1)
    (Nat.succ_ne_zero _)).toLinearEquiv.injective
  change (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1) _).hom _ =
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1) _).hom _
  rw [positiveComplexOrthantRelativeClass_sphere, Complex.OrthantGenerator.positiveComplexOriginalGenerator_sphereBoundary]

end

section

/-! The same actual filling represents the original rational complex generator. -/

open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def positiveComplexOrthantRationalCycle (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)) (2 * p + 2) :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)).hom (2 * p + 2)
    (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ))
      (2 * p + 2) 1 (positiveComplexOrthantRelativeCycle p))

theorem positiveComplexOrthantRationalCycle_val (p : ℕ) :
    (positiveComplexOrthantRationalCycle p).val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)).f (2 * p + 2)
        (ChainRepresentatives.rationalSingularChainElement (TopCat.of (Fin (p + 1) → ℂ)) (2 * p + 2)
          (positiveComplexOrthantFilling p)) :=
  AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeChainsIso_one_tmul_projection (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)
    (2 * p + 2) (positiveComplexOrthantFilling p)

def positiveComplexOrthantRationalClass (p : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin (p + 1) → ℂ)) 0 (2 * (p + 1)) := by
  simpa only [Nat.mul_succ] using
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ))
      (2 * p + 2) (positiveComplexOrthantRationalCycle p)

theorem positiveComplexOrthantRationalClass_coordinate (p : ℕ) :
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso (p + 1)).hom
      (positiveComplexOrthantRationalClass p) = 1 := by
  unfold CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso positiveComplexOrthantRationalClass
  simp only [Nat.mul_succ, id_eq, Iso.trans_hom, ConcreteCategory.comp_apply]
  change CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom
    (CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).hom
      ((CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) (2 * p + 2)).hom
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)) (2 * p + 2)
          (positiveComplexOrthantRationalCycle p)))) = 1
  unfold positiveComplexOrthantRationalCycle
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeHomologyIso_chainClass]
  change CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).hom (positiveComplexOrthantRelativeClass p)) = 1
  rw [positiveComplexOrthantRelativeClass_eq_originalGenerator, Iso.inv_hom_id_apply,
    CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso_hom_one_tmul]
  rfl

theorem positiveComplexOrthantRationalClass_eq_originalGenerator (p : ℕ) :
    positiveComplexOrthantRationalClass p = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator (p + 1) := by
  apply (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso (p + 1)).toLinearEquiv.injective
  change (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso (p + 1)).hom _ =
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso (p + 1)).hom _
  rw [positiveComplexOrthantRationalClass_coordinate]
  exact (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator_normalization (p + 1)).symm

end

section

/-! Injectivity of the actual rational relative boundary and the ordered
complex local-to-sphere map. These are the native connecting maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem rationalRelativeBoundary_injective (X : TopCat.{0}) [ContractibleSpace X]
    (A : Set X) (n : ℕ) :
    Function.Injective ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ X A).δ (n + 1) n rfl) := by
  have hzero : IsZero ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (n + 1)) :=
    CycleClass.Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of ℚ ℚ) X (n + 1) (Nat.succ_ne_zero n)
  have hm := ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ X A).homology_exact₃ (n + 1) n rfl).mono_g
    (hzero.eq_zero_of_src _)
  exact (ModuleCat.mono_iff_injective _).mp hm

def positiveComplexRationalSphereMap (p : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin (p + 1) → ℂ)) 0 (2 * p + 2) ⟶
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (2 * p + 1))).homology (2 * p + 1) :=
  (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)).δ
      (2 * p + 2) (2 * p + 1) rfl ≫
    homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
        (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩)) (2 * p + 1) ≫
    homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p + 2)))))) (2 * p + 1)

theorem positiveComplexRationalSphereMap_injective (p : ℕ) :
    Function.Injective (positiveComplexRationalSphereMap p) := by
  let e := CycleClass.Geometric.ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ)))
    (Y := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p + 2)))))
    (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).toHomotopyEquiv (2 * p + 1)
  have he : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  let s := CycleClass.Geometric.NormalSphereHomology.Cycles.normalSphereSingularHomologyIso (EuclideanSpace ℝ (Fin (2 * p + 2)))
    (ModuleCat.of ℚ ℚ) (2 * p + 1)
  have hs : Function.Injective s.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hs.comp (he.comp (rationalRelativeBoundary_injective (TopCat.of (Fin (p + 1) → ℂ))
    ({0}ᶜ) (2 * p + 1)))

end

/-! The native rational local-to-sphere map sends the actual representative
of the original complex generator to the rational orthant sphere. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def positiveComplexRationalFilling (p : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Fin (p + 1) → ℂ))).X (2 * p + 2) :=
  ChainRepresentatives.rationalSingularChainElement _ (2 * p + 2) (positiveComplexOrthantFilling p)

def positiveComplexRationalBoundaryCycle (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ)))) (2 * p + 1) :=
  ChainRepresentatives.rationalSingularCycle _ (2 * p + 1) (positiveComplexOrthantPuncturedCycle p)

theorem positiveComplexRationalFilling_boundary (p : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Fin (p + 1) → ℂ))).d (2 * p + 2) (2 * p + 1)
      (positiveComplexRationalFilling p) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)).f (2 * p + 1)
        (positiveComplexRationalBoundaryCycle p).val := by
  rw [positiveComplexRationalFilling, ChainRepresentatives.rationalSingularChainElement_d, positiveComplexOrthantFilling_boundary]
  exact (ChainRepresentatives.rationalSingularChainElement_map
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ))
    (2 * p + 1) (positiveComplexOrthantPuncturedCycle p).val).symm

theorem positiveComplexRationalGenerator_boundary (p : ℕ) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)).δ
      (2 * p + 2) (2 * p + 1) rfl
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ))
        (2 * p + 2) (positiveComplexOrthantRationalCycle p)) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
        (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ)))) (2 * p + 1)
        (positiveComplexRationalBoundaryCycle p) :=
  AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives.homologyConnecting_eq_of_lift
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ))
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ))
    (2 * p + 1) (positiveComplexOrthantRationalCycle p) (positiveComplexRationalFilling p)
    (positiveComplexRationalBoundaryCycle p) (positiveComplexOrthantRationalCycle_val p).symm
    (positiveComplexRationalFilling_boundary p).symm

theorem positiveComplexOrthantPuncturedCycle_coordinates_chain (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
      (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
        (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩)) (2 * p + 1)
      (positiveComplexOrthantPuncturedCycle p) = DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p) := by
  apply Subtype.ext
  have hm : CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Positive.ComplexCoordinates.positiveEuclideanToComplexPunctured p) ≫
      CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
          (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Positive.ComplexCoordinates.positiveEuclideanToComplexPunctured_coordinates,
      CategoryTheory.Functor.map_id]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.f (2 * p + 1)) hm)
    (DiskProductSphereGenerator.euclideanOrthantPuncturedCycle (2 * p)).val

theorem positiveComplexRationalBoundaryCycle_coordinates (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
        (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩)) (2 * p + 1)
      (positiveComplexRationalBoundaryCycle p) = DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p) := by
  have h := OrthantSphere.rationalSingularCycle_map
    (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
      (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩) (2 * p + 1)
    (positiveComplexOrthantPuncturedCycle p)
  rw [positiveComplexOrthantPuncturedCycle_coordinates_chain] at h
  exact h

theorem positiveComplexRationalGenerator_sphere (p : ℕ) :
    positiveComplexRationalSphereMap p
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ))
        (2 * p + 2) (positiveComplexOrthantRationalCycle p)) =
      OrthantSphere.rationalOrthantSphereClass (2 * p + 1) := by
  unfold positiveComplexRationalSphereMap
  simp only [ConcreteCategory.comp_apply]
  erw [positiveComplexRationalGenerator_boundary p]
  erw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
    (TopCat.ofHom ⟨Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p,
      (Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates p).continuous⟩)) (2 * p + 1)
    (positiveComplexRationalBoundaryCycle p)]
  rw [positiveComplexRationalBoundaryCycle_coordinates]
  exact DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle_radial (2 * p)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PositiveComplexSphere
