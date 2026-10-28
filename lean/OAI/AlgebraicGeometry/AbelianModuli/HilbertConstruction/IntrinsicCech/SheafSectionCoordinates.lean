/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafTerms.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafEvaluation

/-! # Sheaf Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafSectionCoordinates

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u v w
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X) {ι : Type u}
variable (U : ι → Opens X) (n : ℕ)

noncomputable def cechTermSectionsRawIso (V : Opens X) :
    (SheafTerms.cechTerm F U n).obj.obj (op V) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (SheafTerms.cechTermFactor F U n i).obj.obj (op V) :=
  SheafEvaluation.cechTermForgetSectionsIso F U n V ≪≫ SheafEvaluation.cechTermEvaluationIso F U n V

@[reassoc]
theorem cechTermSectionsRawIso_hom_π (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermSectionsRawIso F U n V).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι =>
          (SheafTerms.cechTermFactor F U n i).obj.obj (op V)) i =
      (Pi.π (SheafTerms.cechTermFactor F U n) i).hom.app (op V) := by
  rw [cechTermSectionsRawIso, Iso.trans_hom, Category.assoc,
    SheafEvaluation.cechTermEvaluationIso_hom_π]
  exact congr_app (SheafForgetProjection.cechTermForgetIso_hom_π F U n i) (op V)

noncomputable def cechTermSectionsProductIso (V : Opens X) :
    (SheafTerms.cechTerm F U n).obj.obj (op V) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  cechTermSectionsRawIso F U n V ≪≫
    Pi.mapIso (SheafTerms.cechTermFactorSectionsIso F U n V)

theorem cechTermSectionsProductIso_hom_π (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermSectionsProductIso F U n V).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι =>
          F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))) i =
      (Pi.π (SheafTerms.cechTermFactor F U n) i).hom.app (op V) ≫
        (SheafTerms.cechTermFactorSectionsIso F U n V i).hom := by
  rw [cechTermSectionsProductIso, Iso.trans_hom, Category.assoc,
    Pi.mapIso_hom_π]
  exact congrArg (fun k ↦ k ≫ (SheafTerms.cechTermFactorSectionsIso F U n V i).hom)
    (cechTermSectionsRawIso_hom_π F U n V i)

/-- Sections of a sheaf-level Cech term are families of sections on tuple intersections. -/
noncomputable def cechTermSectionsAddEquiv (V : Opens X) :
    (SheafTerms.cechTerm F U n).obj.obj (op V) ≃+
      ∀ i : Fin (n + 1) → ι,
        F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  ((cechTermSectionsProductIso F U n V) ≪≫
    Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi fun i : Fin (n + 1) → ι =>
      F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))).addCommGroupIsoToAddEquiv

/-- The component of `cechTermSectionsAddEquiv` at a tuple is restriction to the
corresponding intersection. -/
theorem cechTermSectionsAddEquiv_apply (V : Opens X)
    (x : (SheafTerms.cechTerm F U n).obj.obj (op V)) (i : Fin (n + 1) → ι) :
    cechTermSectionsAddEquiv F U n V x i =
      ((eqToIso (by
          rw [TopologicalSheafRestriction.IntrinsicCech.toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
        (SheafTerms.cechTermFactor F U n i).obj.obj (op V) ≅
          F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))).hom
        ((Pi.π (SheafTerms.cechTermFactor F U n) i).hom.app (op V) x) := by
  rw [show cechTermSectionsAddEquiv F U n V x i =
    (Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi (fun i : Fin (n + 1) → ι =>
      F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))))).hom
        ((cechTermSectionsProductIso F U n V).hom x) i from rfl,
    Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom (cechTermSectionsProductIso_hom_π F U n V i) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafSectionCoordinates
