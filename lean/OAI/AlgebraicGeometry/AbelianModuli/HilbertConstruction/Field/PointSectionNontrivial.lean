import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Point Section Nontrivial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointSectionNontrivial

noncomputable section

/-! A trivial module sheaf on a scheme with an actual field-valued point has nontrivial global sections. The point supplies a map from global functions to a nontrivial field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem trivialModule_globalSections_nontrivial_of_fieldPoint
    {K : Type u} [Field K] {X : Scheme.{u}} (x : Spec (.of K) ⟶ X)
    (M : X.Modules) (e : M ≅ Line.Bundles.structureModule X) : Nontrivial Γ(M, ⊤) := by
  let q : Γ(X, ⊤) →+* K := (Scheme.ΓSpecIso (.of K)).hom.hom.comp x.appTop.hom
  have : Nontrivial Γ(X, ⊤) := q.domain_nontrivial
  let σ : Γ(X, ⊤) → Γ(M, ⊤) := fun r => e.inv.app ⊤ r
  have hσ : Function.Injective σ := by
    intro r s hrs
    have h := congrArg (fun m : Γ(M, ⊤) => e.hom.app ⊤ m) hrs
    have hr : e.hom.app ⊤ (e.inv.app ⊤ r) = r :=
      ConcreteCategory.congr_hom (congrArg (fun f : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X => f.app ⊤)
        e.inv_hom_id) r
    have hs : e.hom.app ⊤ (e.inv.app ⊤ s) = s :=
      ConcreteCategory.congr_hom (congrArg (fun f : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X => f.app ⊤)
        e.inv_hom_id) s
    exact hr.symm.trans (h.trans hs)
  exact ⟨⟨σ 0, σ 1, fun h => zero_ne_one (hσ h)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointSectionNontrivial
