import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndBaseChange

/-! # End Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The scalar of a line-bundle endomorphism is invariant under bundle isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem Line.Bundles.LineBundle.endScalar_transport (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf) (φ : End L.sheaf) :
    M.endScalar (e.inv ≫ φ ≫ e.hom) = L.endScalar φ := by
  have h : e.inv ≫ φ ≫ e.hom = Global.ModuleScalars.globalModuleScalar M.sheaf (L.endScalar φ) := by
    have hφ := Line.Bundles.LineBundle.globalModuleScalar_endScalar L φ
    rw [← hφ, ← Category.assoc, ← Global.ModuleScalars.globalModuleScalar_natural, Category.assoc,
      e.inv_hom_id, Category.comp_id, L.endScalar_globalModuleScalar]
  exact (congrArg M.endScalar h).trans (M.endScalar_globalModuleScalar _)

theorem Line.Bundles.LineBundle.endScalar_transport_eq (L M : Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf)
    (φ : End L.sheaf) (ψ : End M.sheaf) (h : φ ≫ e.hom = e.hom ≫ ψ) :
    L.endScalar φ = M.endScalar ψ := by
  have h' : e.inv ≫ φ ≫ e.hom = ψ :=
    (congrArg (fun k => e.inv ≫ k) h).trans (e.inv_hom_id_assoc ψ)
  exact (Line.Bundles.LineBundle.endScalar_transport L M e φ).symm.trans (congrArg M.endScalar h')

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
