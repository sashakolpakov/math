import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ComplexLocalExactness

/-! # Section Koszul Acyclic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulAcyclic

noncomputable section

/-! A finite family of actual line-bundle sections which contains a frame locally has an exact Koszul complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

theorem lineBundleSectionKoszulComplex_acyclic {X : Scheme.{u}} {ι : Type v}
    (L : Line.Bundles.LineBundle X) (M : X.Modules) (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf))
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hs : ∀ i, ∃ s ∈ ss, IsIso ((Scheme.Modules.pullback (U i).ι).map s)) :
    (SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).Acyclic :=
  Module.ComplexLocalExactness.moduleComplex_acyclic_of_pullback_contractible_cover _ U hU
    (fun i => SectionKoszulComplex.lineBundleSectionKoszulComplex_pullback_contractible L M ss (U i).ι (hs i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulAcyclic
