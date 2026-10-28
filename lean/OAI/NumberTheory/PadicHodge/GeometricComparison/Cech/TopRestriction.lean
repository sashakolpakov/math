import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechAugmentation
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles

/-! # Top Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestriction.CechTopRestriction

noncomputable section

/-! The canonical top-section restriction in degree zero of the original Cech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u w v z
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {ι : Type w} (U : ι → C)
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A)

def map : P.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  Pi.lift (fun t : Fin 1 → ι => P.map (homOfLE (le_top : (∏ᶜ (U ∘ t)) ≤ ⊤)).op)

omit [HasZeroObject A] in
theorem map_comp_d : CechTopRestriction.map C U P ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 :=
  NonemptyCech.Augmentation.NonemptyCechAugmentation.cocycle U P (P.obj (op ⊤)) (Semilattice.CechAugmentation.SemilatticeCechAugmentation.cone C P)

def initial : ShortComplex A :=
  ShortComplex.mk (CechTopRestriction.map C U P) (((cechComplexFunctor U).obj P).d 0 1) (map_comp_d C U P)

def augmentation : (CochainComplex.single₀ A).obj (P.obj (op ⊤)) ⟶ (cechComplexFunctor U).obj P :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨CechTopRestriction.map C U P, map_comp_d C U P⟩

theorem augmentation_zero : (augmentation C U P).f 0 = CechTopRestriction.map C U P :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

variable (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
  {κ : Type u} (V : κ → Opens X) (hV : iSup V = ⊤)

include hV

theorem eq_original : CechTopRestriction.map (Opens X) V F.obj = AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation V F := by
  apply AddCommGrpCat.ext
  intro a
  apply (AlgebraicGeometry.SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj V 0).injective
  funext t
  have h := AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv_coordinate V F hV a t
  change AlgebraicGeometry.SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj V 0 (AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation V F a) t = _ at h
  rw [h, AlgebraicGeometry.SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply]
  exact ConcreteCategory.congr_hom (Pi.lift_comp_π
    (fun t : Fin 1 → κ => F.obj.map (homOfLE (le_top : (∏ᶜ (V ∘ t)) ≤ ⊤)).op) t) a

theorem mono : Mono (CechTopRestriction.map (Opens X) V F.obj) := by
  rw [eq_original X F V hV]
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro a b hab
  exact (AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsToZeroCycles_bijective V F hV).1 (Subtype.ext hab)

theorem exact : (ShortComplex.mk (CechTopRestriction.map (Opens X) V F.obj)
    (((cechComplexFunctor V).obj F.obj).d 0 1) (map_comp_d (Opens X) V F.obj)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  obtain ⟨a, ha⟩ := (AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsToZeroCycles_bijective V F hV).2 ⟨x, hx⟩
  refine ⟨a, ?_⟩
  change CechTopRestriction.map (Opens X) V F.obj a = x
  rw [eq_original X F V hV]
  exact congrArg Subtype.val ha

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestriction.CechTopRestriction
