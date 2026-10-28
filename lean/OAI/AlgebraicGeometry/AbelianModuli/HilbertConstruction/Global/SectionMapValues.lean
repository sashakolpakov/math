import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Section Map Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionMapValues

noncomputable section

/-! A section viewed as a module-sheaf morphism acts on each open by multiplying its restricted value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem moduleSectionHomEquiv_symm_app (M : X.Modules) (z : Γ(M, ⊤)) (V : X.Opens) (r : Γ(X, V)) :
    ((Sections.moduleSectionHomEquiv M).symm z).app V r =
      r • M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op z := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionMapValues
