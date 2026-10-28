import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport

/-! # Scalar Maps -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps

noncomputable section

/-! Germs and stalk maps respect the actual coefficient-field actions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

def germ (f : X ⟶ Spec (.of K)) (U : X.Opens) (x : X) (hx : x ∈ U) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    letI := PointAlgebra.scalarAlgebra f x
    Γ(X, U) →ₐ[K] X.presheaf.stalk x := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := PointAlgebra.scalarAlgebra f x
  refine { (X.presheaf.germ U x hx).hom with commutes' := ?_ }
  intro c
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hx) c =
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) c
  have he : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hx =
      f.appTop ≫ X.presheaf.germ ⊤ x trivial := by
    change (f.app ⊤ ≫ X.presheaf.map (homOfLE le_top).op) ≫ X.presheaf.germ U x hx =
      f.app ⊤ ≫ X.presheaf.germ ⊤ x trivial
    rw [Category.assoc, TopCat.Presheaf.germ_res]
  rw [he]

theorem germ_apply (f : X ⟶ Spec (.of K)) (U : X.Opens) (x : X) (hx : x ∈ U) (r : Γ(X, U)) :
    ScalarMaps.germ f U x hx r = X.presheaf.germ U x hx r := rfl

def stalk (i : X ⟶ Y) (f : Y ⟶ Spec (.of K)) (x : X) :
    letI := PointAlgebra.scalarAlgebra f (i x)
    letI := PointAlgebra.scalarAlgebra (i ≫ f) x
    Y.presheaf.stalk (i x) →ₐ[K] X.presheaf.stalk x := by
  let := PointAlgebra.scalarAlgebra f (i x)
  let := PointAlgebra.scalarAlgebra (i ≫ f) x
  refine { (i.stalkMap x).hom with commutes' := ?_ }
  intro c
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    Y.presheaf.germ ⊤ _ trivial ≫ i.stalkMap x) c =
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ f).appTop ≫ X.presheaf.germ ⊤ x trivial) c
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
  rfl

theorem stalk_surjective (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Spec (.of K)) (x : X) :
    Function.Surjective (ScalarMaps.stalk i f x) := by
  exact i.stalkMap_surjective x

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps
