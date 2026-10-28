import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.SerreVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Serre Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A projective embedding supplied by a positive power of an actual line bundle gives uniform vanishing along multiples of that degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.tensorPowers_eventually_vanish
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m → ∀ q : ℕ,
      IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).obj
        (Tensor.ProductSheaf.tensorModule M (L.tensorPower (m * E.degree)).sheaf)) := by
  let i := SectionsProjectiveMorphism.sectionProjectiveMorphism f E.sections E.covers
  have : IsClosedImmersion i.left := E.closedImmersion
  obtain ⟨B, hB⟩ := RelativeProjective.SerreVanishing.relativeEmbedding_tensorTwistingPowers_eventually_vanish i M
  let eP := (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some
  refine ⟨B, fun m hm q ↦ ?_⟩
  let eT := (TensorPower.Maps.tensorPowerFunctor X m).mapIso (E.twistingBundleIso f ≪≫ eP) ≪≫
    (L.tensorPowerComposeIso m E.degree).symm
  exact (hB m hm q).of_iso
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).mapIso
      (Tensor.ProductSheaf.tensorModuleCongr (Iso.refl M) eT)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
