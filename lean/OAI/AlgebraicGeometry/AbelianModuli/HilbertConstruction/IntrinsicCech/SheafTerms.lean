/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafTerms.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction

/-! # Sheaf Terms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafTerms

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u v w
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X) {ι : Type u}
variable (U : ι → Opens X) (n : ℕ)

/-- The restriction-pushforward factor in a sheaf-level Cech term. -/
noncomputable abbrev cechTermFactor (i : Fin (n + 1) → ι) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat
    (∏ᶜ fun k : Fin (n + 1) => U (i k)).isOpenEmbedding ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat
      (∏ᶜ fun k : Fin (n + 1) => U (i k)).inclusion').obj F

/-- Degree `n` of the sheaf-level Cech resolution associated to the open family `U`. -/
noncomputable def cechTerm : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ∏ᶜ cechTermFactor F U n

noncomputable def cechTermFactorSectionsIso (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermFactor F U n i).obj.obj (op V) ≅
      F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  eqToIso (by
    rw [TopologicalSheafRestriction.IntrinsicCech.toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])

noncomputable def cechTermForgetDiagramIso :
    Discrete.functor (cechTermFactor F U n) ⋙ TopCat.Sheaf.forget AddCommGrpCat X ≅
      Discrete.functor fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj :=
  Discrete.natIso (fun _ => Iso.refl _)

noncomputable def cechTermForgetIso :
    (cechTerm F U n).obj ≅
      ∏ᶜ fun i : Fin (n + 1) → ι => (cechTermFactor F U n i).obj := by
  letI : HasLimit (Discrete.functor (cechTermFactor F U n) ⋙
      TopCat.Sheaf.forget AddCommGrpCat X) :=
    hasLimit_of_iso (cechTermForgetDiagramIso F U n).symm
  exact preservesLimitIso (TopCat.Sheaf.forget AddCommGrpCat X)
      (Discrete.functor (cechTermFactor F U n)) ≪≫
    HasLimit.isoOfNatIso (cechTermForgetDiagramIso F U n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafTerms
