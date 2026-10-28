import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # Dual Line -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualLine.Construction.DualLineBundle

noncomputable section

/-! The actual sheaf dual of an FiniteDescent line bundle is again a line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

variable {X : Scheme.{u}}

/-- Local frames for a line bundle also frame its sheaf of linear functionals. -/
def dual (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := SheafCohomology.Projective.Dual.Scheme.Modules.dualObj L.sheaf
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
    refine ⟨U, hx, ⟨?_⟩⟩
    exact SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackIsoOfRestrictIso _ U
      (SheafCohomology.Projective.Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso L.sheaf U
        (SheafCohomology.Projective.Invertible.Scheme.Modules.restrictIsoOfPullbackIso L.sheaf U e))

/-- Dualization respects isomorphisms of line bundles. -/
def congr {L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X} (e : L.sheaf ≅ M.sheaf) :
    (dual M).sheaf ≅ (dual L).sheaf :=
  SheafCohomology.Projective.Dual.Scheme.Modules.dualIsoObj e

/-- The dual of the trivial line bundle is trivial. -/
def unitIso : (dual (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  SheafCohomology.Projective.Dual.Scheme.Modules.dualUnitObjIso

/-- Duals of isomorphic bundles determine the same line-bundle class. -/
def dualClass (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X :=
  Quotient.liftOn q (fun L => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (dual L)) (by
    intro L M ⟨e⟩
    exact Quotient.sound ⟨congr e.symm⟩)

theorem dualClass_trivial :
    dualClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X :=
  Quotient.sound ⟨unitIso⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualLine.Construction.DualLineBundle
