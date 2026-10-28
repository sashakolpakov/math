import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UniversalCocycleProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues

/-! # Scheme Cocycle Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleRecovery

noncomputable section

/-! The universal tensor coordinate recovers the original geometric cocycle on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocyclePoints OAI.AlgebraicGeometry.Picard.PoincareBundle.UniversalCocycleProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues

variable (k R : Type u) [CommRing k] [CommRing R] [HopfAlgebra k R]
  (C : NaturalSchemeCocycle.NaturalCocycle ((Spec (.of R)).asOver (Spec (.of k))))

/-- The actual tensor coefficient of the geometric cocycle. -/
def coordinate : (R ⊗[k] R)ˣ :=
  NaturalAlgebraCocycle.coordinate k R (SchemeCocycleCoordinates.algebraCocycle k R C)

/-- The coordinate regular unit is exactly the original coefficient on the universal product. -/
theorem coefficientUnit_eq :
    Finite.CocycleSchemeValues.coefficientUnit k R (coordinate k R C) =
      C.value (fst ((Spec (.of R)).asOver (Spec (.of k))) ((Spec (.of R)).asOver (Spec (.of k))))
        (snd ((Spec (.of R)).asOver (Spec (.of k))) ((Spec (.of R)).asOver (Spec (.of k)))) := by
  let G := (Spec (.of R)).asOver (Spec (.of k))
  let e := pullbackSpecIso k R R
  have hn := C.natural (UniversalCocycleProduct.universalPair k R) (fst G G) (snd G G)
  rw [UniversalCocycleProduct.universalPair_fst, UniversalCocycleProduct.universalPair_snd] at hn
  have hv := congrArg Units.val hn
  change (UniversalCocycleProduct.universalPair k R).left.appTop (C.value (fst G G) (snd G G)).val = _ at hv
  rw [UniversalCocycleProduct.universalPair_left] at hv
  have : IsIso e.inv.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.inv.op))
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso e.inv.appTop).injective
  have hc : e.inv.appTop (Finite.CocycleSchemeValues.coefficientUnit k R (coordinate k R C)).val =
      (Finite.CocycleSchemeValues.coordinateUnit (R ⊗[k] R) (coordinate k R C)).val := by
    change (e.inv ≫ e.hom).appTop _ = _
    rw [e.inv_hom_id]
    rfl
  have hrecover : (Finite.CocycleSchemeValues.coordinateUnit (R ⊗[k] R) (coordinate k R C)).val =
      (C.value (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeLeft)
        (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeRight)).val :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (R ⊗[k] R))).hom_inv_id
      (C.value (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeLeft)
        (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeRight)).val
  exact hc.trans (hrecover.trans hv.symm)

/-- Recovery holds for arbitrary test schemes, including nonaffine and nonreduced ones. -/
theorem value_eq (T : Over (Spec (.of k)))
    (x y : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) :
    Finite.CocycleSchemeValues.value k R (coordinate k R C) T x y = C.value x y := by
  let G := (Spec (.of R)).asOver (Spec (.of k))
  let φ : Γ((G ⊗ G).left, ⊤)ˣ →* Γ(T.left, ⊤)ˣ := Units.map (lift x y).left.appTop.hom
  have h := C.natural (lift x y) (fst G G) (snd G G)
  have hp := congrArg₂ (fun a b : T ⟶ G => C.value a b) (lift_fst x y) (lift_snd x y)
  exact (congrArg φ (coefficientUnit_eq k R C)).trans (h.trans hp)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleRecovery
