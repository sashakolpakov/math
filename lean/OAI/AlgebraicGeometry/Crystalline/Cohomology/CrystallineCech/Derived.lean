import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Resolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Derived -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Derived.CrystallineCechDerived

noncomputable section

/-!
# Native crystalline cohomology through the frame Čech resolution

The checked sheaf resolution is placed in nonpositive cohomological
degrees. Its canonical augmentation identifies it with the native
coefficient sheaf in the derived category. Precomposition gives a
linear equivalence from the existing Ext definition, for every degree
and every coefficient sheaf.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (A : Type u) [CommRing A] [Algebra (WittVector p k) A]
  (r : A →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) A) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X

abbrev Sheaves := Sheaf J (ModuleCat.{u + 1} R)

local instance derivedCategory : HasDerivedCategory.{u + 2} (Sheaves p k B) :=
  HasDerivedCategory.standard _

def complex : CochainComplex (Sheaves p k B) ℤ :=
  (Resolution.CrystallineCechResolution.complex p k B A r hr hbase).extend ComplexShape.embeddingDownNat

def augmentedSingleIso :
    ((ChainComplex.single₀ (Sheaves p k B)).obj (Site.coefficientSheaf p k X)).extend
      ComplexShape.embeddingDownNat ≅
        (HomologicalComplex.single (Sheaves p k B) (ComplexShape.up ℤ) 0).obj (Site.coefficientSheaf p k X) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
    (Site.coefficientSheaf p k X) 0 0 rfl

def augmentation : complex p k B A r hr hbase ⟶
    (HomologicalComplex.single (Sheaves p k B) (ComplexShape.up ℤ) 0).obj
      (Site.coefficientSheaf p k X) :=
  HomologicalComplex.extendMap (Resolution.CrystallineCechResolution.augmentation p k B A r hr hbase)
      ComplexShape.embeddingDownNat ≫ (augmentedSingleIso p k B).hom

variable [Algebra.Smooth (WittVector p k) A]

instance augmentation_quasiIso : QuasiIso (augmentation p k B A r hr hbase) := by
  have h : QuasiIso (Resolution.CrystallineCechResolution.augmentation p k B A r hr hbase) :=
    Resolution.CrystallineCechResolution.augmentation_quasiIso p k B A r hr hbase
  exact quasiIso_comp
    (HomologicalComplex.extendMap (Resolution.CrystallineCechResolution.augmentation p k B A r hr hbase)
      ComplexShape.embeddingDownNat) (augmentedSingleIso p k B).hom

/-- The frame resolution represents the actual coefficient sheaf in the derived category. -/
def derivedIso : DerivedCategory.Q.obj (complex p k B A r hr hbase) ≅
    (DerivedCategory.singleFunctor (Sheaves p k B) 0).obj (Site.coefficientSheaf p k X) := by
  have h : IsIso (DerivedCategory.Q.map (augmentation p k B A r hr hbase)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Sheaves p k B) (augmentation p k B A r hr hbase)).mpr
      (augmentation_quasiIso p k B A r hr hbase)
  exact @asIso _ _ _ _ (DerivedCategory.Q.map (augmentation p k B A r hr hbase)) h

/-- The native Ext groups, with arbitrary coefficient sheaf, expressed using the fixed frame. -/
def cohomologyEquiv (M : Sheaves p k B) (n : ℕ) :
    Abelian.Ext (Site.coefficientSheaf p k X) M n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj (complex p k B A r hr hbase))
        ((DerivedCategory.singleFunctor (Sheaves p k B) 0).obj M) (n : ℤ) :=
  Abelian.Ext.homLinearEquiv.trans
    (Linear.homCongr R (derivedIso p k B A r hr hbase).symm (Iso.refl _))

theorem cohomologyEquiv_apply (M : Sheaves p k B) (n : ℕ)
    (a : Abelian.Ext (Site.coefficientSheaf p k X) M n) :
    cohomologyEquiv p k B A r hr hbase M n a = (derivedIso p k B A r hr hbase).hom ≫ a.hom := by
  change ((derivedIso p k B A r hr hbase).hom ≫ a.hom) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Changing coefficient sheaves commutes with the comparison to the frame resolution. -/
theorem cohomologyEquiv_postcomp {M N : Sheaves p k B} (g : M ⟶ N) (n : ℕ)
    (a : Abelian.Ext (Site.coefficientSheaf p k X) M n) :
    cohomologyEquiv p k B A r hr hbase N n (a.comp (Abelian.Ext.mk₀ g) (Nat.add_zero n)) =
      cohomologyEquiv p k B A r hr hbase M n a ≫
        (shiftFunctor (DerivedCategory (Sheaves p k B)) (n : ℤ)).map
          ((DerivedCategory.singleFunctor (Sheaves p k B) 0).map g) := by
  rw [cohomologyEquiv_apply, cohomologyEquiv_apply,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀, Category.assoc]

/-- In particular this is the existing integral crystalline cohomology, not a replacement definition. -/
def integralCohomologyEquiv (n : ℕ) :
    Site.integralCohomology p k X n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj (complex p k B A r hr hbase))
        ((DerivedCategory.singleFunctor (Sheaves p k B) 0).obj
          (Site.structureSheaf p k X)) (n : ℤ) :=
  cohomologyEquiv p k B A r hr hbase (Site.structureSheaf p k X) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Derived.CrystallineCechDerived
