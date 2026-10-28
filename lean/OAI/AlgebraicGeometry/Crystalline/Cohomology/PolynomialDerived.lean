import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Polynomial Derived -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialDerived.CrystallinePolynomialDerived

noncomputable section

/-!
# Native crystalline cohomology through polynomial coordinate forms

The actual structure-sheaf resolution is placed in nonnegative integer
degrees. Its proved augmentation is invertible in the derived category.
Postcomposition identifies the original native Ext groups with derived
morphisms into this coordinate resolution, in every degree.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (σ : Type u) [Fintype σ]

local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k

abbrev Sheaves := PolynomialSheafResolution.CrystallinePolynomialSheafResolution.Sheaves p k X

local instance derivedCategory : HasDerivedCategory.{u + 2} (Sheaves p k X) :=
  HasDerivedCategory.standard _

def complex : CochainComplex (Sheaves p k X) ℤ :=
  (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.complex p k X σ).extend ComplexShape.embeddingUpNat

def singleIso :
    ((CochainComplex.single₀ (Sheaves p k X)).obj (Site.structureSheaf p k X)).extend
      ComplexShape.embeddingUpNat ≅
        (HomologicalComplex.single (Sheaves p k X) (ComplexShape.up ℤ) 0).obj
          (Site.structureSheaf p k X) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (Site.structureSheaf p k X) 0 0 rfl

def augmentation :
    (HomologicalComplex.single (Sheaves p k X) (ComplexShape.up ℤ) 0).obj
      (Site.structureSheaf p k X) ⟶ complex p k X σ :=
  (singleIso p k X).inv ≫ HomologicalComplex.extendMap
    (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.augmentation p k X σ) ComplexShape.embeddingUpNat

instance augmentation_quasiIso : QuasiIso (augmentation p k X σ) :=
  quasiIso_comp (singleIso p k X).inv (HomologicalComplex.extendMap
    (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.augmentation p k X σ) ComplexShape.embeddingUpNat)

/-- The polynomial coordinate complex represents the actual native structure sheaf. -/
def derivedIso : (DerivedCategory.singleFunctor (Sheaves p k X) 0).obj
    (Site.structureSheaf p k X) ≅ DerivedCategory.Q.obj (complex p k X σ) := by
  have h : IsIso (DerivedCategory.Q.map (augmentation p k X σ)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Sheaves p k X) (augmentation p k X σ)).mpr
      (augmentation_quasiIso p k X σ)
  exact @asIso _ _ _ _ (DerivedCategory.Q.map (augmentation p k X σ)) h

/-- A linear equivalence from Cohomology's original integral crystalline cohomology. -/
def integralCohomologyEquiv (n : ℕ) : Site.integralCohomology p k X n ≃ₗ[R]
    ShiftedHom ((DerivedCategory.singleFunctor (Sheaves p k X) 0).obj
      (Site.coefficientSheaf p k X)) (DerivedCategory.Q.obj (complex p k X σ)) (n : ℤ) :=
  Abelian.Ext.homLinearEquiv.trans
    (Linear.homCongr R (Iso.refl _) ((shiftFunctor (DerivedCategory (Sheaves p k X)) (n : ℤ)).mapIso
      (derivedIso p k X σ)))

theorem integralCohomologyEquiv_apply (n : ℕ) (a : Site.integralCohomology p k X n) :
    integralCohomologyEquiv p k X σ n a = a.hom ≫
      (shiftFunctor (DerivedCategory (Sheaves p k X)) (n : ℤ)).map (derivedIso p k X σ).hom := by
  change (𝟙 _ ≫ a.hom) ≫ _ = _
  rw [Category.id_comp]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialDerived.CrystallinePolynomialDerived
