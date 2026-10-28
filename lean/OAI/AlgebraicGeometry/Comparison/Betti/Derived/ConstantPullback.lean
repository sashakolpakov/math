import OAI.AlgebraicGeometry.Comparison.Betti.Derived.DerivedSheafBetti
import OAI.AlgebraicGeometry.Comparison.Betti.TopologicalSheafPullback

/-! # Constant Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.ConstantPullback

noncomputable section

/-! Actual derived inverse-image pullback on constant-sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {M N : TopCat.{0}} (f : M ⟶ N)

instance sheafDirectImageLinear : (TopologicalSheafPullback.sheafDirectImage f).Linear ℂ where
  map_smul := by intros; rfl

instance sheafInverseImageLinear : (TopologicalSheafPullback.sheafInverseImage f).Linear ℂ where
  map_smul {A B} c g := by
    let adj := TopologicalSheafPullback.sheafImageAdjunction f
    apply (adj.homEquiv A ((TopologicalSheafPullback.sheafInverseImage f).obj B)).injective
    have hmap (k : A ⟶ B) :
        adj.homEquiv A ((TopologicalSheafPullback.sheafInverseImage f).obj B) ((TopologicalSheafPullback.sheafInverseImage f).map k) =
          k ≫ adj.unit.app B := by
      simpa only [Category.comp_id, adj.homEquiv_id] using
        adj.homEquiv_naturality_left k (𝟙 ((TopologicalSheafPullback.sheafInverseImage f).obj B))
    rw [hmap, Linear.smul_comp, adj.homEquiv_unit,
      Functor.map_smul, Linear.comp_smul, ← adj.homEquiv_unit, hmap]

def derivedConstantPullbackIso :
    (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves N) 0).obj (ConstantSheafSections.standardConstantSheaf N)) ≅
      (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).obj (ConstantSheafSections.standardConstantSheaf M) :=
  ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategorySingleFunctor 0).app (ConstantSheafSections.standardConstantSheaf N) ≪≫
    (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).mapIso (TopologicalSheafPullback.constantPullbackIso f)

def constantDerivedPullback (n : ℕ) : DerivedSheafBetti.constantDerivedCohomology N n ⟶ DerivedSheafBetti.constantDerivedCohomology M n :=
  ModuleCat.ofHom
    { toFun := fun a => (derivedConstantPullbackIso f).inv ≫
        ShiftedHom.map a (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory ≫
          ((derivedConstantPullbackIso f).hom)⟦(n : ℤ)⟧'
      map_add' := by
        intro a b
        simp only [ShiftedHom.map, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro c a
        simp only [ShiftedHom.map, Functor.map_smul, Linear.comp_smul, Linear.smul_comp,
          RingHom.id_apply] }

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.ConstantPullback
