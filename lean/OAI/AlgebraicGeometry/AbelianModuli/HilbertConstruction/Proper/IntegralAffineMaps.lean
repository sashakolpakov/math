import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralGlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FactorThroughConstants

/-! # Integral Affine Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralAffineMaps

noncomputable section

/-! Maps from integral universally closed schemes to affine schemes factor through the algebraically closed base field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}

theorem properIntegral_affineFactorization (p : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed p] (f : X ⟶ Y) [IsAffine Y] :
    ∃! a : Spec (.of K) ⟶ Y, p ≫ a = f := by
  let : IsIso p.appTop := IntegralGlobalSections.properIntegral_appTop_isIso p
  exact Affine.FactorThroughConstants.affineFactorOfGlobalIso_existsUnique p f

theorem properIntegral_map_eq_constant (p : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed p] (f : X ⟶ Y) [IsAffine Y]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) : f = p ≫ x ≫ f := by
  obtain ⟨a, ha, _⟩ := properIntegral_affineFactorization p f
  have hxa : x ≫ f = a := by rw [← ha, ← Category.assoc, hx, Category.id_comp]
  exact ha.symm.trans (congrArg (fun b => p ≫ b) hxa.symm)

theorem properIntegral_affineMap_eq_iff_atPoint (p : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed p] [IsAffine Y]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) (f h : X ⟶ Y) :
    f = h ↔ x ≫ f = x ≫ h := by
  constructor
  · exact congrArg (fun k => x ≫ k)
  · intro H
    exact (properIntegral_map_eq_constant p f x hx).trans
      ((congrArg (fun k => p ≫ k) H).trans (properIntegral_map_eq_constant p h x hx).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralAffineMaps
