import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues

/-! # Cocycle Scheme Equation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSchemeEquation

noncomputable section

/-! The tensor coboundary equation holds as an equality of regular functions on the group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars

variable (k R : Type u) [CommRing k] [CommRing R] [HopfAlgebra k R]
  (c : (R ⊗[k] R)ˣ) (a : Rˣ)
  (hΔ : (c : R ⊗[k] R) * Coalgebra.comul (a : R) = (a : R) ⊗ₜ[k] (a : R))

include hΔ

/-- Equality on the universal product scheme, before specializing to test points. -/
theorem product_section :
    (Finite.CocycleSchemeValues.coefficientUnit k R c).val *
      μ[(Spec (.of R)).asOver (Spec (.of k))].left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R)) =
    (fst ((Spec (.of R)).asOver (Spec (.of k)))
      ((Spec (.of R)).asOver (Spec (.of k)))).left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R)) *
    (snd ((Spec (.of R)).asOver (Spec (.of k)))
      ((Spec (.of R)).asOver (Spec (.of k)))).left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R)) := by
  let G := (Spec (.of R)).asOver (Spec (.of k))
  let e := pullbackSpecIso k R R
  have : IsIso e.inv.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.inv.op))
  apply (ConcreteCategory.bijective_of_isIso e.inv.appTop).injective
  erw [e.inv.appTop.hom.map_mul, e.inv.appTop.hom.map_mul]
  have hc : e.inv.appTop (Finite.CocycleSchemeValues.coefficientUnit k R c).val =
      AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection (R ⊗[k] R) (c : R ⊗[k] R) := by
    change (e.inv ≫ e.hom).appTop _ = _
    rw [e.inv_hom_id]
    rfl
  have hm : e.inv ≫ μ[G].left =
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k R).toRingHom) := by
    rw [mul_spec_asOver_spec_left]
    exact e.inv_hom_id_assoc _
  have hl : e.inv ≫ (fst G G).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] R)) :=
    pullbackSpecIso_inv_fst k R R
  have hr : e.inv ≫ (snd G G).left =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : R →ₐ[k] R ⊗[k] R).toRingHom) :=
    pullbackSpecIso_inv_snd k R R
  have hm' := (congrArg (fun f => f.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))) hm).trans
    (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection_pullback (Bialgebra.comulAlgHom k R).toRingHom (a : R))
  have hl' := (congrArg (fun f => f.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))) hl).trans
    (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection_pullback (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] R) (a : R))
  have hr' := (congrArg (fun f => f.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))) hr).trans
    (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection_pullback
      (Algebra.TensorProduct.includeRight : R →ₐ[k] R ⊗[k] R).toRingHom (a : R))
  rw [hc]
  change _ * (e.inv ≫ μ[G].left).appTop _ =
    (e.inv ≫ (fst G G).left).appTop _ * (e.inv ≫ (snd G G).left).appTop _
  rw [hm', hl', hr']
  change (Scheme.ΓSpecIso (.of (R ⊗[k] R))).inv.hom _ *
      (Scheme.ΓSpecIso (.of (R ⊗[k] R))).inv.hom _ =
    (Scheme.ΓSpecIso (.of (R ⊗[k] R))).inv.hom _ *
      (Scheme.ΓSpecIso (.of (R ⊗[k] R))).inv.hom _
  rw [← map_mul, ← map_mul]
  apply congrArg (Scheme.ΓSpecIso (.of (R ⊗[k] R))).inv.hom
  exact hΔ.trans (by
    change (a : R) ⊗ₜ[k] (a : R) = ((a : R) ⊗ₜ[k] (1 : R)) * ((1 : R) ⊗ₜ[k] (a : R))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul])

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSchemeEquation
