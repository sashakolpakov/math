import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Section Value Additive -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive

noncomputable section

/-! Global values of module-sheaf sections preserve finite sums. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def moduleSectionValueAddHom {X : Scheme.{u}} (M : X.Modules) :
    (Line.Bundles.structureModule X ⟶ M) →+ Γ(M, ⊤) where
  toFun := Global.Sections.moduleSectionHomEquiv M
  map_zero' := rfl
  map_add' _ _ := rfl

theorem moduleSectionHomEquiv_sum {X : Scheme.{u}} (M : X.Modules)
    {ι : Type v} (I : Finset ι) (s : ι → (Line.Bundles.structureModule X ⟶ M)) :
    Global.Sections.moduleSectionHomEquiv M (∑ i ∈ I, s i) = ∑ i ∈ I, Global.Sections.moduleSectionHomEquiv M (s i) :=
  map_sum (moduleSectionValueAddHom M) s I

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
