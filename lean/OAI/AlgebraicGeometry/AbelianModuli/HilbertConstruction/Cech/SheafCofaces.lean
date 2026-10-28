/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafDifferential.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafFactorRestriction

/-! # Sheaf Cofaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafCofaces.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X) (n : ℕ)

theorem cechTupleLE (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (n + 1) =>
        U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i)

/-- The sheaf-level Cech coface obtained by deleting the `k`th entry of every tuple. -/
noncomputable def cechCoface (k : Fin (n + 2)) :
    IntrinsicCech.SheafTerms.cechTerm F U n ⟶ IntrinsicCech.SheafTerms.cechTerm F U (n + 1) :=
  Pi.lift (fun i : Fin (n + 2) → ι =>
    Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U n)
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F (cechTupleLE U n k i))

/-- Under the concrete section equivalence, a sheaf-level Cech coface restricts the
component indexed by the tuple with its `k`th entry deleted. -/
theorem cechCoface_apply (V : Opens X) (x : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op V))
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V
        ((cechCoface F U n k).hom.app (op V) x) i =
      F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
        (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V x
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv_apply]
  have hcoface :
      cechCoface F U n k ≫ Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U (n + 1)) i =
        Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F (cechTupleLE U n k i) := by
    change
      Pi.lift (fun i : Fin (n + 2) → ι =>
          Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U n)
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
            SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F (cechTupleLE U n k i)) ≫
          Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U (n + 1)) i =
        Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F (cechTupleLE U n k i)
    exact Pi.lift_comp_π _ i
  have hcomponent :
      (Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U (n + 1)) i).hom.app (op V)
          ((cechCoface F U n k).hom.app (op V) x) =
        (SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F (cechTupleLE U n k i)).hom.app (op V)
          ((Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app (op V) x) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op V)) hcoface) x
  rw [hcomponent, SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction_apply,
    ← IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv_apply]
  exact ConcreteCategory.congr_hom
    (congrArg F.obj.map (Subsingleton.elim _ _))
    (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V x
      (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafCofaces.IntrinsicCech
