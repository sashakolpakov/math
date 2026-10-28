import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TraceRetraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Trace Cohomology Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TraceCohomologyVanishing

noncomputable section

/-! Along an affine map with a trace retraction, vanishing of the pulled-back line bundle's genuine cohomology descends to the original line bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem affine_lineBundle_cohomology_vanishes_of_pullback
    {X Y : Scheme.{u}} [X.IsSeparated] {R : Type u} [CommRing R]
    (f : Y ⟶ X) [IsAffineHom f] (p : X ⟶ Spec (.of R)) (L : Line.Bundles.LineBundle X)
    (hs : IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf))
    (q : ℕ)
    (hz : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ p)) q).obj
      (L.pullback f).sheaf)) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj L.sheaf) := by
  have : ((L.pullback f).sheaf).IsQuasicoherent := (L.pullback f).isQuasicoherent
  let F := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q
  let η : L.sheaf ⟶ (Scheme.Modules.pushforward f).obj (L.pullback f).sheaf :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf
  obtain ⟨⟨r, hr⟩⟩ := hs
  have hη : IsSplitMono (F.map η) := ⟨⟨F.map r,
    (F.map_comp η r).symm.trans ((congrArg F.map hr).trans (F.map_id L.sheaf))⟩⟩
  have hz' : IsZero (F.obj ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf)) :=
    hz.of_iso (PushforwardCohomologyFiniteness.affinePushforwardCohomologyIso f p (L.pullback f).sheaf q).symm
  exact IsZero.of_mono (F.map η) hz'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TraceCohomologyVanishing
