import OAI.AlgebraicGeometry.AbelianVariety.PowerCohomology
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular

/-! # Doubling Difference -/

namespace OAI.AlgebraicGeometry.AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

abbrev abelianPointTop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := Betti.Scheme.schemePointSpace A.toOver
abbrev abelianPointProductTop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  TopCat.of (abelianPointTop A × abelianPointTop A)

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : CommGroup (abelianPointTop A) :=
  inferInstanceAs (CommGroup A.variety.analyticSpace)
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsTopologicalGroup (abelianPointTop A) :=
  AnalyticGroup.Constructions.ExteriorCohomology.pointTopologicalGroup A

def abelianMulTop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : abelianPointProductTop A ⟶ abelianPointTop A :=
  TopCat.ofHom ⟨fun z => z.1 * z.2,
    (show Continuous (fun z : A.variety.analyticSpace × A.variety.analyticSpace => z.1 * z.2)
      from continuous_mul)⟩
def abelianDiagTop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : abelianPointTop A ⟶ abelianPointProductTop A :=
  TopCat.ofHom ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩
def abelianInsertFirstTop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : abelianPointTop A ⟶ abelianPointProductTop A :=
  TopCat.ofHom ⟨fun x => (x, 1), continuous_id.prodMk continuous_const⟩
def abelianInsertSecondTop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : abelianPointTop A ⟶ abelianPointProductTop A :=
  TopCat.ofHom ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩
def abelianPowTop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (k : ℕ) : abelianPointTop A ⟶ abelianPointTop A :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k)

@[simp] theorem abelianPowTop_apply (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (k : ℕ) (x : abelianPointTop A) :
    abelianPowTop A k x = x ^ k := PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism_point A k x

@[simp] theorem diag_mul (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianDiagTop A ≫ abelianMulTop A = abelianPowTop A 2 := by
  apply TopCat.ext
  intro x
  change x * x = _
  simp [pow_two]
@[simp] theorem first_mul (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianInsertFirstTop A ≫ abelianMulTop A = 𝟙 (abelianPointTop A) := by
  apply TopCat.ext
  intro x
  exact mul_one x
@[simp] theorem second_mul (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianInsertSecondTop A ≫ abelianMulTop A = 𝟙 (abelianPointTop A) := by
  apply TopCat.ext
  intro x
  exact one_mul x
@[simp] theorem diag_fst (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianDiagTop A ≫ TopCat.prodFst = 𝟙 (abelianPointTop A) := rfl
@[simp] theorem diag_snd (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianDiagTop A ≫ TopCat.prodSnd = 𝟙 (abelianPointTop A) := rfl
@[simp] theorem first_fst (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianInsertFirstTop A ≫ TopCat.prodFst = 𝟙 (abelianPointTop A) := rfl
@[simp] theorem first_snd (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianInsertFirstTop A ≫ TopCat.prodSnd = abelianPowTop A 0 := by
  apply TopCat.ext
  intro x
  change 1 = _
  simp
@[simp] theorem second_fst (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianInsertSecondTop A ≫ TopCat.prodFst = abelianPowTop A 0 := by
  apply TopCat.ext
  intro x
  change 1 = _
  simp
@[simp] theorem second_snd (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianInsertSecondTop A ≫ TopCat.prodSnd = 𝟙 (abelianPointTop A) := rfl

theorem pullback_comp_apply {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Z n) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g n a) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (f ≫ g) n a :=
  (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp _ f g n) a).symm

@[simp] theorem abelianPowTop_pullback (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (k n : ℕ)
    (a : A.variety.rationalCohomology n) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (abelianPowTop A k) n a =
      (k : ℚ) ^ n • a := PowerCohomology.Constructions.Exterior.abelianPower_rationalBetti A k n a

def doublingDifference (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (abelianPointProductTop A) n →ₗ[ℚ]
      A.variety.rationalCohomology n :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (abelianDiagTop A) n).hom -
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (abelianInsertFirstTop A) n).hom -
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (abelianInsertSecondTop A) n).hom

theorem doublingDifference_mulPullback (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (a : A.variety.rationalCohomology n) :
    doublingDifference A n (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (abelianMulTop A) n a) =
      ((2 : ℚ) ^ n - 2) • a := by
  simp only [doublingDifference, LinearMap.sub_apply,
    pullback_comp_apply, diag_mul, first_mul, second_mul, abelianPowTop_pullback,
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, ConcreteCategory.id_apply]
  module

theorem doublingDifference_cross (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (a : A.variety.rationalCohomology p) (b : A.variety.rationalCohomology q) :
    doublingDifference A (p + q)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (abelianPointProductTop A) p q
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst p a)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd q b)) =
      (1 - (0 : ℚ) ^ q - (0 : ℚ) ^ p) •
        AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (abelianPointTop A) p q a b := by
  simp only [doublingDifference, LinearMap.sub_apply,
    AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback, pullback_comp_apply,
    diag_fst, diag_snd, first_fst, first_snd, second_fst, second_snd,
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, ConcreteCategory.id_apply, abelianPowTop_pullback,
    map_smul, LinearMap.smul_apply]
  module

end

end OAI.AlgebraicGeometry.AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology
