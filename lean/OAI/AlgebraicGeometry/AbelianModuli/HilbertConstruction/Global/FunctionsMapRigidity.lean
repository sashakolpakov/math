import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants

/-! # Functions Map Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity

noncomputable section

/-! Global-function isomorphisms force affine-valued maps to factor through a section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X T Y : Scheme.{u}}

theorem affineMap_eq_of_globalFunctions_iso (p : X ⟶ T) [IsIso p.appTop]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 _) (f : X ⟶ Y) [IsAffine Y] :
    f = p ≫ σ ≫ f := by
  obtain ⟨a, ha, _⟩ := Affine.FactorThroughConstants.affineFactorOfGlobalIso_existsUnique p f
  have hσa : σ ≫ f = a := by rw [← ha, ← Category.assoc, hσ, Category.id_comp]
  exact ha.symm.trans (congrArg (fun b => p ≫ b) hσa.symm)

theorem properField_baseChange_affineMap_eq {K : Type u} [Field K] {P : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ T} {t : T ⟶ Spec (.of K)} (H : IsPullback a b p t)
    (σ : T ⟶ P) (hσ : σ ≫ b = 𝟙 _) (f : P ⟶ Y) [IsAffine Y] :
    f = b ≫ σ ≫ f := by
  have := Proper.FieldBaseChangeConstants.properField_baseChange_globalFunctions_isIso p x hx H
  exact affineMap_eq_of_globalFunctions_iso b σ hσ f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity
