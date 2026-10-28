import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechContraction
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Cech Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechAugmentation.SemilatticeCechAugmentation

noncomputable section

/-! The checked split Čech contraction uses the canonical restriction
augmentation, including its actual degree-zero cochain map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u w v z
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {ι : Type w} (U : ι → C)
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A)

def cone : (Functor.const Cᵒᵖ).obj (P.obj (op ⊤)) ⟶ P where
  app V := P.map (homOfLE (le_top : V.unop ≤ ⊤)).op
  naturality _ _ α := by
    change 𝟙 _ ≫ P.map _ = P.map _ ≫ P.map _
    exact (Category.id_comp _).trans
      ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

def augmentation : (CochainComplex.single₀ A).obj (P.obj (op ⊤)) ⟶
    (IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P :=
  NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P (P.obj (op ⊤)) (cone C P)

variable (i₀ : ι) (hU : U i₀ = ⊤)

theorem hom_zero : (CechContraction.SemilatticeCechContraction.homotopyEquiv C U i₀ hU P).hom.f 0 =
    (NonemptyCech.Augmentation.NonemptyCechAugmentation.restriction U P (P.obj (op ⊤)) (cone C P)).app ⦋0⦌ := by
  dsimp only [CechContraction.SemilatticeCechContraction.homotopyEquiv, HomotopyEquiv.symm, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite.unop, HomologicalComplex.unopFunctor,
    HomologicalComplex.comp_f, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite.cofaceIso, AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite.singleIso,
    HomologicalComplex.Hom.isoOfComponents]
  change ((CochainComplex.single₀ A).map (CechContraction.SemilatticeCechContraction.pointIso C P).inv).f 0 ≫
    (𝟙 _ ≫ ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering _ _).obj
        (((FormalCoproduct.evalOp C A).obj P).rightOp)).obj
          (CechContraction.SemilatticeCechContraction.augmented C U))).f 0).unop ≫ 𝟙 _) = _
  rw [CochainComplex.single₀_map_f_zero, AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  simp only [Category.id_comp]
  change (CechContraction.SemilatticeCechContraction.pointIso C P).inv ≫
    (𝟙 _ ≫ ((FormalCoproduct.evalOp C A).obj P).map
      ((CechContraction.SemilatticeCechContraction.augmented C U).hom.app (op ⦋0⦌)).op) ≫ 𝟙 _ = _
  simp only [Category.comp_id]
  erw [Category.id_comp]
  change Pi.lift (fun _ : PUnit.{w + 1} => 𝟙 (P.obj (op ⊤))) ≫
      Pi.lift (fun i : Fin 1 → ι => Pi.π (fun _ : PUnit.{w + 1} => P.obj (op ⊤)) PUnit.unit ≫
        P.map (homOfLE (le_top : (∏ᶜ (U ∘ i)) ≤ ⊤)).op) =
    Pi.lift (fun i : Fin 1 → ι => P.map (homOfLE (le_top : (∏ᶜ (U ∘ i)) ≤ ⊤)).op)
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Category.id_comp]

theorem hom_eq : (CechContraction.SemilatticeCechContraction.homotopyEquiv C U i₀ hU P).hom = augmentation C U P := by
  apply HomologicalComplex.from_single_hom_ext
  exact (hom_zero C U P i₀ hU).trans
    (NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero U P (P.obj (op ⊤)) (cone C P)).symm

include hU in
theorem quasiIso [CategoryWithHomology A] : QuasiIso (augmentation C U P) := by
  rw [← hom_eq C U P i₀ hU]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechAugmentation.SemilatticeCechAugmentation
