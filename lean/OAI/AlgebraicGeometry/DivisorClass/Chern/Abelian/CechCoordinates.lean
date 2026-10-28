import OAI.AlgebraicGeometry.SheafCohomology.Cech.Differential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

/-! # Cech Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechCoordinates

noncomputable section

/-! Native abelian Cech cochains in the original literal-intersection coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (F : X.Presheaf AddCommGrpCat.{0}) (U : I → Opens X)

abbrev AbelianCechCochain (n : ℕ) :=
  ∀ a : Fin (n + 1) → I, F.obj (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))

def abelianCechIntersectionIso {n : ℕ} (a : Fin (n + 1) → I) :
    F.obj (op (∏ᶜ fun j => U (a j))) ≅ F.obj (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) :=
  F.mapIso (eqToIso (congrArg op (SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf (fun j => U (a j)))))

def abelianCechCoordinates (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F).X n ≃+ AbelianCechCochain F U n :=
  (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F U n).trans
    (AddEquiv.piCongrRight (fun a => (abelianCechIntersectionIso F U a).addCommGroupIsoToAddEquiv))

theorem abelianCechCoordinates_apply (n : ℕ)
    (x : ((CategoryTheory.cechComplexFunctor U).obj F).X n) (a : Fin (n + 1) → I) :
    abelianCechCoordinates F U n x a =
      (abelianCechIntersectionIso F U a).hom (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F U n x a) := rfl

def abelianCechDelta (n : ℕ) (c : AbelianCechCochain F U n) : AbelianCechCochain F U (n + 1) :=
  fun a => ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)).op (c (a ∘ j.succAbove))

theorem abelianCechCoordinates_d (n : ℕ)
    (x : ((CategoryTheory.cechComplexFunctor U).obj F).X n) :
    abelianCechCoordinates F U (n + 1)
        (((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1) x) =
      abelianCechDelta F U n (abelianCechCoordinates F U n x) := by
  funext a
  rw [abelianCechCoordinates_apply, SheafCohomology.Cech.Differential.TopologicalSpace.cechDifferential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1
  have he :
      F.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ j).toOrderHom.toFun).φ a).op ≫
        (abelianCechIntersectionIso F U a).hom =
      (abelianCechIntersectionIso F U (a ∘ j.succAbove)).hom ≫
        F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)).op := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom he (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F U n x (a ∘ j.succAbove))

theorem abelianCechCoordinates_naturality
    {G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G) (n : ℕ)
    (x : ((CategoryTheory.cechComplexFunctor U).obj F).X n) (a : Fin (n + 1) → I) :
    abelianCechCoordinates G U n (((CategoryTheory.cechComplexFunctor U).map f).f n x) a =
      f.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) (abelianCechCoordinates F U n x a) := by
  have hn : SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv G U n
        (((CategoryTheory.cechComplexFunctor U).map f).f n x) a =
      f.app (op (∏ᶜ fun j => U (a j))) (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F U n x a) := by
    rw [SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply, SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply]
    exact ConcreteCategory.congr_hom
      (Limits.Pi.map_π (fun b : Fin (n + 1) → I =>
        f.app (op (∏ᶜ fun j => U (b j)))) a) x
  rw [abelianCechCoordinates_apply, hn, abelianCechCoordinates_apply]
  exact (ConcreteCategory.congr_hom (f.naturality _)
    (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F U n x a)).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechCoordinates
