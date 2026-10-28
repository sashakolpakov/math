import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SerreVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness

/-! # Line Cohomology Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineCohomologyVanishing

noncomputable section

/-! All positive genuine cohomology groups of sufficiently high powers of an ample line bundle vanish uniformly. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem ample_lineBundle_eventually_vanish
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (L : Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n → ∀ q : ℕ,
      IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).obj
        (L.tensorPower n).sheaf) := by
  have : (Line.Bundles.structureModule X).IsQuasicoherent := (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have : (Line.Bundles.structureModule X).IsFiniteType := (Line.Bundles.LineBundle.trivial X).isFiniteType
  obtain ⟨B, hB⟩ := SerreVanishing.ample_tensorPowers_eventually_vanish f L hL (Line.Bundles.structureModule X)
  exact ⟨B, fun n hn q ↦ (hB n hn q).of_iso
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).mapIso
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso (L.tensorPower n).sheaf)).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineCohomologyVanishing
