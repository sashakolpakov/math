import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology

/-! # Cech Classes -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses

noncomputable section

/-! Actual sheaf classes of literal-intersection abelian Cech cocycles. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

def abelianCechCoefficient {F G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G) (n : ℕ)
    (k : CechCoordinates.AbelianCechCochain F U n) : CechCoordinates.AbelianCechCochain G U n :=
  fun a => f.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) (k a)

theorem abelianCechCoefficient_delta {F G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G) (n : ℕ)
    (k : CechCoordinates.AbelianCechCochain F U n) :
    abelianCechCoefficient U f (n + 1) (CechCoordinates.abelianCechDelta F U n k) =
      CechCoordinates.abelianCechDelta G U n (abelianCechCoefficient U f n k) := by
  funext a
  dsimp only [abelianCechCoefficient, CechCoordinates.abelianCechDelta]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1
  exact ConcreteCategory.congr_hom (f.naturality _) (k (a ∘ j.succAbove))

theorem abelianCechCoefficient_closed {F G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G)
    (n : ℕ) (k : CechCoordinates.AbelianCechCochain F U n) (hk : CechCoordinates.abelianCechDelta F U n k = 0) :
    CechCoordinates.abelianCechDelta G U n (abelianCechCoefficient U f n k) = 0 := by
  rw [← abelianCechCoefficient_delta, hk]
  funext a
  exact map_zero (f.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom

theorem abelianCechNative_closed (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : CechCoordinates.AbelianCechCochain F U n) (hk : CechCoordinates.abelianCechDelta F U n k = 0) :
    ((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1)
      ((CechCoordinates.abelianCechCoordinates F U n).symm k) = 0 := by
  apply (CechCoordinates.abelianCechCoordinates F U (n + 1)).injective
  rw [CechCoordinates.abelianCechCoordinates_d, AddEquiv.apply_symm_apply, hk, map_zero]

theorem abelianCechDelta_nsmul (F : X.Presheaf AddCommGrpCat.{0}) (n N : ℕ)
    (k : CechCoordinates.AbelianCechCochain F U n) :
    CechCoordinates.abelianCechDelta F U n (N • k) = N • CechCoordinates.abelianCechDelta F U n k := by
  calc
    _ = CechCoordinates.abelianCechCoordinates F U (n + 1)
        (((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1)
          ((CechCoordinates.abelianCechCoordinates F U n).symm (N • k))) := by
      rw [CechCoordinates.abelianCechCoordinates_d, AddEquiv.apply_symm_apply]
    _ = N • CechCoordinates.abelianCechCoordinates F U (n + 1)
        (((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1)
          ((CechCoordinates.abelianCechCoordinates F U n).symm k)) := by
      rw [map_nsmul, map_nsmul, map_nsmul]
    _ = _ := by rw [CechCoordinates.abelianCechCoordinates_d, AddEquiv.apply_symm_apply]

theorem abelianCechDelta_nsmul_closed (F : X.Presheaf AddCommGrpCat.{0}) (n N : ℕ)
    (k : CechCoordinates.AbelianCechCochain F U n) (hk : CechCoordinates.abelianCechDelta F U n k = 0) :
    CechCoordinates.abelianCechDelta F U n (N • k) = 0 := by
  rw [abelianCechDelta_nsmul, hk, smul_zero]

def abelianCechNativeClass (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : CechCoordinates.AbelianCechCochain F U (n + 1)) (hk : CechCoordinates.abelianCechDelta F U (n + 1) k = 0) :
    ((CategoryTheory.cechComplexFunctor U).obj F).homology (n + 1) :=
  ((CategoryTheory.cechComplexFunctor U).obj F).homologyπ (n + 1)
    (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ ((CechCoordinates.abelianCechCoordinates F U (n + 1)).symm k)
      (abelianCechNative_closed U F (n + 1) k hk))

def abelianCechSheafClass (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) (k : CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (hk : CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0) : CategoryTheory.Sheaf.H F (n + 1) :=
  CechComparison.abelianCechToSheaf U F hU n (abelianCechNativeClass U F.obj n k hk)

theorem abelianCechNativeClass_nsmul (F : X.Presheaf AddCommGrpCat.{0}) (n N : ℕ)
    (k : CechCoordinates.AbelianCechCochain F U (n + 1)) (hk : CechCoordinates.abelianCechDelta F U (n + 1) k = 0) :
    abelianCechNativeClass U F n (N • k) (abelianCechDelta_nsmul_closed U F (n + 1) N k hk) =
      N • abelianCechNativeClass U F n k hk := by
  let L := (CategoryTheory.cechComplexFunctor U).obj F
  have he : SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n L ((CechCoordinates.abelianCechCoordinates F U (n + 1)).symm (N • k))
        (abelianCechNative_closed U F (n + 1) (N • k)
          (abelianCechDelta_nsmul_closed U F (n + 1) N k hk)) =
      N • SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n L ((CechCoordinates.abelianCechCoordinates F U (n + 1)).symm k)
        (abelianCechNative_closed U F (n + 1) k hk) := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles (n + 1))).mp inferInstance
    rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, map_nsmul, map_nsmul, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  unfold abelianCechNativeClass
  rw [he, map_nsmul]

theorem abelianCechSheafClass_nsmul (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (n N : ℕ)
    (k : CechCoordinates.AbelianCechCochain F.obj U (n + 1)) (hk : CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0) :
    abelianCechSheafClass U F hU n (N • k)
        (abelianCechDelta_nsmul_closed U F.obj (n + 1) N k hk) =
      N • abelianCechSheafClass U F hU n k hk := by
  unfold abelianCechSheafClass
  rw [abelianCechNativeClass_nsmul, map_nsmul]

theorem abelianCechNativeClass_naturality {F G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G)
    (n : ℕ) (k : CechCoordinates.AbelianCechCochain F U (n + 1)) (hk : CechCoordinates.abelianCechDelta F U (n + 1) k = 0) :
    HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map f) (n + 1)
        (abelianCechNativeClass U F n k hk) =
      abelianCechNativeClass U G n (abelianCechCoefficient U f (n + 1) k)
        (abelianCechCoefficient_closed U f (n + 1) k hk) := by
  let L := (CategoryTheory.cechComplexFunctor U).obj F
  let M := (CategoryTheory.cechComplexFunctor U).obj G
  let phi := (CategoryTheory.cechComplexFunctor U).map f
  let x := (CechCoordinates.abelianCechCoordinates F U (n + 1)).symm k
  have hx := abelianCechNative_closed U F (n + 1) k hk
  have hfx : M.d (n + 1) (n + 2) (phi.f (n + 1) x) = 0 := by
    have h := ConcreteCategory.congr_hom (phi.comm (n + 1) (n + 2)) x
    change M.d (n + 1) (n + 2) (phi.f (n + 1) x) =
      phi.f (n + 2) (L.d (n + 1) (n + 2) x) at h
    erw [hx, map_zero] at h
    exact h
  have he : phi.f (n + 1) x =
      (CechCoordinates.abelianCechCoordinates G U (n + 1)).symm (abelianCechCoefficient U f (n + 1) k) := by
    apply (CechCoordinates.abelianCechCoordinates G U (n + 1)).injective
    rw [AddEquiv.apply_symm_apply]
    funext a
    rw [CechCoordinates.abelianCechCoordinates_naturality, AddEquiv.apply_symm_apply]
    rfl
  unfold abelianCechNativeClass
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n phi x hx hfx]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (M.iCycles (n + 1))).mp inferInstance
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  exact he

theorem abelianCechSheafClass_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (hU : ⨆ i, U i = ⊤) (n : ℕ)
    (k : CechCoordinates.AbelianCechCochain F.obj U (n + 1)) (hk : CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0) :
    CategoryTheory.Sheaf.H.map f (n + 1) (abelianCechSheafClass U F hU n k hk) =
      abelianCechSheafClass U G hU n (abelianCechCoefficient U f.hom (n + 1) k)
        (abelianCechCoefficient_closed U f.hom (n + 1) k hk) := by
  have h := ConcreteCategory.congr_hom (CechComparison.abelianCechToSheaf_naturality U f hU n)
    (abelianCechNativeClass U F.obj n k hk)
  change CechComparison.abelianCechToSheaf U G hU n
      (HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map f.hom) (n + 1)
        (abelianCechNativeClass U F.obj n k hk)) = _ at h
  rw [abelianCechNativeClass_naturality] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses
