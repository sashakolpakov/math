import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf

/-! # Cocycle Scheme Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues

noncomputable section

/-! Actual regular-unit values of a tensor cocycle and its solution on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

/-- An invertible coordinate gives an invertible global regular function on its spectrum. -/
def coordinateUnit (R : Type u) [CommRing R] (a : Rˣ) : Γ(Spec (.of R), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom a

variable (k R : Type u) [CommRing k] [CommRing R] [HopfAlgebra k R]

/-- The tensor coordinate is transported to the actual fiber product scheme. -/
def coefficientUnit (c : (R ⊗[k] R)ˣ) :
    Γ((((Spec (.of R)).asOver (Spec (.of k))) ⊗
      ((Spec (.of R)).asOver (Spec (.of k)))).left, ⊤)ˣ :=
  Units.map (pullbackSpecIso k R R).hom.appTop.hom.toMonoidHom (coordinateUnit (R ⊗[k] R) c)

/-- Pulling back the regular coefficient evaluates the cocycle on any pair of test points. -/
def value (c : (R ⊗[k] R)ˣ) (T : Over (Spec (.of k)))
    (x y : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) : Γ(T.left, ⊤)ˣ :=
  Units.map (lift x y).left.appTop.hom.toMonoidHom (coefficientUnit k R c)

/-- The solution unit gives a regular frame adjustment on every test scheme. -/
def solution (a : Rˣ) (T : Over (Spec (.of k)))
    (x : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) : Γ(T.left, ⊤)ˣ :=
  Units.map x.left.appTop.hom.toMonoidHom (coordinateUnit R a)

theorem solution_natural (a : Rˣ) {T U : Over (Spec (.of k))} (f : U ⟶ T)
    (x : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) :
    Units.map f.left.appTop.hom.toMonoidHom (solution k R a T x) =
      solution k R a U (f ≫ x) := by
  apply Units.ext
  rfl

theorem value_natural (c : (R ⊗[k] R)ˣ) {T U : Over (Spec (.of k))} (f : U ⟶ T)
    (x y : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) :
    Units.map f.left.appTop.hom.toMonoidHom (value k R c T x y) =
      value k R c U (f ≫ x) (f ≫ y) := by
  apply Units.ext
  change (f ≫ lift x y).left.appTop (coefficientUnit k R c : Γ(_, ⊤)) = _
  rw [comp_lift]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues
