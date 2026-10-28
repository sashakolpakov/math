import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseAmpleAcyclicity

/-! # Ample Restriction Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmpleRestrictionAcyclicity

noncomputable section

/-! Relative ampleness makes high powers acyclic on the actual inverse image of each affine open of a locally Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem relativelyAmple_restrictedPowers_eventually_acyclic
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (L : Line.Bundles.LineBundle X) (hL : L.IsRelativelyAmple f)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n → ∀ q : ℕ,
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((L.tensorPower n).sheaf.restrict (f ⁻¹ᵁ U).ι) (q + 1)) := by
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let V := f ⁻¹ᵁ U
  obtain ⟨B, hB⟩ := Affine.BaseAmpleAcyclicity.ample_lineBundle_eventually_acyclic_affine
    (f ∣_ U) (L.pullback V.ι) (hL U hU)
  refine ⟨B, fun n hn q ↦ ?_⟩
  have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((L.pullback V.ι).tensorPower n).sheaf (q + 1)) := hB n hn q
  let e : (L.tensorPower n).sheaf.restrict V.ι ≅ ((L.pullback V.ι).tensorPower n).sheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (L.tensorPower n).sheaf ≪≫
      L.powerBaseChangeIso V.ι n
  exact (ConcreteCategory.bijective_of_isIso
    ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor V.toScheme (q + 1)).map e.hom)).injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmpleRestrictionAcyclicity
