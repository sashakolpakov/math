import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TraceCohomologyVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ScalingDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineCohomologyVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Expanding Line Bundle Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExpandingLineBundleCohomology

noncomputable section

/-! Trace and an expanding pullback convert Serre's eventual vanishing into vanishing of every positive power of an ample line bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem ample_lineBundle_allPowers_vanish_of_expanding_pullback
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} [X.IsSeparated]
    (p : X ⟶ Spec (.of R)) [IsProper p] (f : X ⟶ X) [IsAffineHom f]
    (hf : f ≫ p = p) (L : Line.Bundles.LineBundle X) (hL : L.IsAmple) {d : ℕ} (hd : 1 < d)
    (e : (L.pullback f).sheaf ≅ (L.tensorPower d).sheaf)
    (hs : ∀ Q : Line.Bundles.LineBundle X, IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Q.sheaf))
    (m : ℕ) (hm : 0 < m) (q : ℕ) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)).obj (L.tensorPower m).sheaf) := by
  let F := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)
  obtain ⟨B, hB⟩ := Ample.LineCohomologyVanishing.ample_lineBundle_eventually_vanish p L hL
  apply Power.ScalingDescent.powerScalingDescent (fun a => IsZero (F.obj (L.tensorPower a).sheaf)) hd ?_
    ⟨B, fun a ha => hB a ha q⟩ m hm
  intro a ha
  let ea : ((L.tensorPower a).pullback f).sheaf ≅ (L.tensorPower (a * d)).sheaf :=
    Line.Bundles.LineBundle.powerBaseChangeIso f L a ≪≫ (TensorPower.Maps.tensorPowerFunctor X a).mapIso e ≪≫
      (L.tensorPowerComposeIso a d).symm
  have hpull : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ p)) (q + 1)).obj
      ((L.tensorPower a).pullback f).sheaf) := by
    rw [hf]
    exact ha.of_iso (F.mapIso ea)
  exact Affine.TraceCohomologyVanishing.affine_lineBundle_cohomology_vanishes_of_pullback f p (L.tensorPower a)
    (hs (L.tensorPower a)) (q + 1) hpull

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExpandingLineBundleCohomology
