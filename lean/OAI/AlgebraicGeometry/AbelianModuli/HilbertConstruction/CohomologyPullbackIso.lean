import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionAdjunction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Cohomology Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso

noncomputable section

/-! Pullback along a scheme isomorphism preserves genuine line-bundle cohomology with its structural coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def lineBundleCohomologyPullbackIso
    {X Y : Scheme.{u}} [Y.IsSeparated] {R : Type u} [CommRing R]
    (f : X ⟶ Y) [IsIso f] (p : Y ⟶ Spec (.of R)) (L : Line.Bundles.LineBundle Y) (q : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ p)) q).obj
        (L.pullback f).sheaf ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj L.sheaf := by
  have : (L.pullback f).sheaf.IsQuasicoherent := (L.pullback f).isQuasicoherent
  have : (Scheme.Modules.pullback f).IsEquivalence := Affine.SectionAdjunction.AffineSectionAdjunction.pullback_equivalence (asIso f)
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf
  have : IsIso η := inferInstance
  exact Affine.PushforwardCohomologyFiniteness.affinePushforwardCohomologyIso f p (L.pullback f).sheaf q ≪≫
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).mapIso (asIso η).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso
