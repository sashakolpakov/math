import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialDerived

/-! # Derived -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Derived.CrystallineFrameDerived

noncomputable section

/-!
# Native crystalline cohomology through an actual polynomial frame

The constructed frame resolution represents the actual native structure
sheaf in the derived category. This identifies the original crystalline
Ext groups with derived morphisms into the frame-coordinate complex.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k

abbrev Sheaves := PolynomialSheafResolution.CrystallinePolynomialSheafResolution.Sheaves p k X

local instance derivedCategory : HasDerivedCategory.{u + 2} (Sheaves p k B) :=
  HasDerivedCategory.standard _

def complex : CochainComplex (Sheaves p k B) ℤ :=
  (SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).extend ComplexShape.embeddingUpNat

def augmentation :
    (HomologicalComplex.single (Sheaves p k B) (ComplexShape.up ℤ) 0).obj
      (Site.structureSheaf p k X) ⟶ complex p k B σ a :=
  (PolynomialDerived.CrystallinePolynomialDerived.singleIso p k X).inv ≫ HomologicalComplex.extendMap
    (SheafResolution.CrystallineFrameSheafResolution.augmentation p k B σ a) ComplexShape.embeddingUpNat

instance augmentation_quasiIso : QuasiIso (augmentation p k B σ a) :=
  quasiIso_comp (PolynomialDerived.CrystallinePolynomialDerived.singleIso p k X).inv (HomologicalComplex.extendMap
    (SheafResolution.CrystallineFrameSheafResolution.augmentation p k B σ a) ComplexShape.embeddingUpNat)

def derivedIso : (DerivedCategory.singleFunctor (Sheaves p k B) 0).obj
    (Site.structureSheaf p k X) ≅ DerivedCategory.Q.obj (complex p k B σ a) := by
  have h : IsIso (DerivedCategory.Q.map (augmentation p k B σ a)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Sheaves p k B) (augmentation p k B σ a)).mpr
      (augmentation_quasiIso p k B σ a)
  exact @asIso _ _ _ _ (DerivedCategory.Q.map (augmentation p k B σ a)) h

/-- The domain is Cohomology's original integral crystalline cohomology. -/
def integralCohomologyEquiv (n : ℕ) : Site.integralCohomology p k X n ≃ₗ[R]
    ShiftedHom ((DerivedCategory.singleFunctor (Sheaves p k B) 0).obj
      (Site.coefficientSheaf p k X)) (DerivedCategory.Q.obj (complex p k B σ a)) (n : ℤ) :=
  Abelian.Ext.homLinearEquiv.trans
    (Linear.homCongr R (Iso.refl _) ((shiftFunctor (DerivedCategory (Sheaves p k B)) (n : ℤ)).mapIso
      (derivedIso p k B σ a)))

theorem integralCohomologyEquiv_apply (n : ℕ) (t : Site.integralCohomology p k X n) :
    integralCohomologyEquiv p k B σ a n t = t.hom ≫
      (shiftFunctor (DerivedCategory (Sheaves p k B)) (n : ℤ)).map (derivedIso p k B σ a).hom := by
  change (𝟙 _ ≫ t.hom) ≫ _ = _
  rw [Category.id_comp]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Derived.CrystallineFrameDerived
