import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.CechComparison
import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Obj -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

noncomputable section

/-!
# ChernClass: actual rational singular classes from locally constant Cech cocycles

The map evaluates locally constant functions as singular zero-cochains,
includes them in the Cech total complex, and inverts the proved rational
singular restriction isomorphism. It therefore uses the existing singular
cohomology. Cech coboundaries have equal resulting singular classes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

/-- Locally constant rational functions with their usual restriction maps. -/
abbrev locallyConstantPresheaf (X : TopCat.{u}) : X.Presheaf (ModuleCat.{u} ℚ) where
  obj U := ModuleCat.of ℚ (LocallyConstant U.unop ℚ)
  map i := ModuleCat.ofHom {
    toFun := fun f => ⟨fun x => f (i.unop x),
      f.isLocallyConstant.comp_continuous
        (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl

@[simp]
theorem locallyConstantPresheaf_obj (X : TopCat.{u}) (U : Opens X) :
    (locallyConstantPresheaf X).obj (op U) = ModuleCat.of ℚ (LocallyConstant U ℚ) := rfl

@[simp]
theorem locallyConstantPresheaf_map_apply {X : TopCat.{u}} {U V : Opens X}
    (h : V ≤ U) (f : LocallyConstant U ℚ) (x : V) :
    LocallyConstant.toFun ((locallyConstantPresheaf X).map (homOfLE h).op f) x =
      f ⟨x, h x.property⟩ := rfl

/-- Rational locally constant functions evaluate as actual singular zero-cochains. -/
def locallyConstantSingularAugmentation (X : TopCat.{0}) :
    locallyConstantPresheaf X ⟶
      AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0 where
  app U := AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U.unop)
  naturality _U _V i :=
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_naturality (ModuleCat.of ℚ ℚ)
      ((Opens.toTopCat X).map i.unop)

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X)

/-- Evaluate a Cech cochain of locally constant functions in singular degree zero. -/
abbrev locallyConstantCechEvaluation (p : ℕ) :=
  Rational.Cech.RationalCech.cechCoefficientMap U (locallyConstantSingularAugmentation X) p

theorem locallyConstantCechEvaluation_vertical_zero (p : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (locallyConstantPresheaf X) U p) :
    Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) p
      (locallyConstantCechEvaluation X U p c) = 0 := by
  funext a
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_d (ModuleCat.of ℚ ℚ)
      (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) (c a)

/-- The actual inclusion of locally constant Cech cochains into the total complex. -/
def locallyConstantCechToTotal :
    Rational.Cech.RationalCech.cechComplex (locallyConstantPresheaf X) U ⟶
      Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ) :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom (locallyConstantCechEvaluation X U p) ≫
      Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
        p 0 p (Nat.add_zero p))
    (fun p => by
      apply ConcreteCategory.ext_apply
      intro c
      change Rational.Cech.RationalCech.CechCochain (locallyConstantPresheaf X) U p at c
      have h := ConcreteCategory.congr_hom
        (Rational.Cech.RationalCech.cechTotalInclusion_d U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
          p 0 p (Nat.add_zero p)) (locallyConstantCechEvaluation X U p c)
      change (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d p (p + 1)
          (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
            p 0 p _ (locallyConstantCechEvaluation X U p c)) =
        Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
          (p + 1) 0 (p + 1) _
          (Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U p
            (locallyConstantCechEvaluation X U p c)) +
        (-1 : ℤ) ^ p •
          Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
            p 1 (p + 1) _
            (Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) p
              (locallyConstantCechEvaluation X U p c)) at h
      rw [locallyConstantCechEvaluation_vertical_zero, map_zero, smul_zero, add_zero] at h
      rw [← Rational.Cech.RationalCech.cechCoefficientMap_delta] at h
      rw [Rational.Cech.RationalCech.cechComplex_d]
      convert h using 1)

/-- The induced map lands in the existing rational singular cohomology. -/
def cechCohomologyToSingular
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (Rational.Cech.RationalCech.cechComplex (locallyConstantPresheaf X) U).homology n ⟶
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n :=
  HomologicalComplex.homologyMap (locallyConstantCechToTotal X U) n ≫
    (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hcover n).inv

/-- The actual rational singular class of a locally constant Cech cocycle. -/
def singularClassOfCechCocycle
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (locallyConstantPresheaf X) U) n) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n :=
  cechCohomologyToSingular X U hcover n
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (locallyConstantPresheaf X) U) n c)

/-- A Cech coboundary does not change the resulting rational singular class. -/
theorem singularClassOfCechCocycle_eq_of_boundary
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (c d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (locallyConstantPresheaf X) U) (n + 1))
    (b : Rational.Cech.RationalCech.CechCochain (locallyConstantPresheaf X) U n)
    (hb : Rational.Cech.RationalCech.cechDelta (locallyConstantPresheaf X) U n b = c.val - d.val) :
    singularClassOfCechCocycle X U hcover (n + 1) c =
      singularClassOfCechCocycle X U hcover (n + 1) d := by
  apply congrArg (cechCohomologyToSingular X U hcover (n + 1))
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ
    (Rational.Cech.RationalCech.cechComplex (locallyConstantPresheaf X) U) n c d).mpr
  refine ⟨b, ?_⟩
  rw [Rational.Cech.RationalCech.cechComplex_d]
  exact hb

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj
