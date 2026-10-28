import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSchemeEquation

/-! # Cocycle Scheme Solution -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSchemeSolution

noncomputable section

/-! The cocycle solution is normalized and multiplicative on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars

variable (k R : Type u) [CommRing k] [CommRing R] [HopfAlgebra k R]

/-- The tensor equation specializes to the actual unit-valued equation on every pair of points. -/
theorem solution_mul (c : (R ⊗[k] R)ˣ) (a : Rˣ)
    (hΔ : (c : R ⊗[k] R) * Coalgebra.comul (a : R) = (a : R) ⊗ₜ[k] (a : R))
    (T : Over (Spec (.of k))) (x y : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) :
    Finite.CocycleSchemeValues.value k R c T x y * Finite.CocycleSchemeValues.solution k R a T (x * y) = Finite.CocycleSchemeValues.solution k R a T x * Finite.CocycleSchemeValues.solution k R a T y := by
  let G := (Spec (.of R)).asOver (Spec (.of k))
  let q : T ⟶ G ⊗ G := lift x y
  have hm : (x * y).left = q.left ≫ μ[G].left := rfl
  have hl : q.left ≫ (fst G G).left = x.left := congrArg Over.Hom.left (lift_fst x y)
  have hr : q.left ≫ (snd G G).left = y.left := congrArg Over.Hom.left (lift_snd x y)
  apply Units.ext
  change q.left.appTop (Finite.CocycleSchemeValues.coefficientUnit k R c).val *
      (x * y).left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R)) =
    x.left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R)) * y.left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))
  rw [hm]
  change q.left.appTop (Finite.CocycleSchemeValues.coefficientUnit k R c).val *
    q.left.appTop (μ[G].left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))) = _
  erw [← q.left.appTop.hom.map_mul, CocycleSchemeEquation.product_section k R c a hΔ,
    q.left.appTop.hom.map_mul]
  exact congrArg₂ (· * ·)
    (congrArg (fun f => f.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))) hl)
    (congrArg (fun f => f.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))) hr)

/-- The counit normalization gives value one at the identity on every test scheme. -/
theorem solution_one (a : Rˣ) (hε : Coalgebra.counit (R := k) (a : R) = 1)
    (T : Over (Spec (.of k))) :
    Finite.CocycleSchemeValues.solution k R a T (1 : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) = 1 := by
  have h := AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection_pullback (Bialgebra.counitAlgHom k R).toRingHom (a : R)
  have hη : η[(Spec (.of R)).asOver (Spec (.of k))].left.appTop
      (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R)) = 1 :=
    h.trans ((congrArg (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection k) hε).trans (Scheme.ΓSpecIso (.of k)).inv.hom.map_one)
  apply Units.ext
  change (toUnit T).left.appTop
    (η[(Spec (.of R)).asOver (Spec (.of k))].left.appTop (AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection R (a : R))) = 1
  rw [hη, map_one]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSchemeSolution
