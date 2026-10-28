import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatGenerationNeighborhood
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleAllVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Ample Fiber Power Generation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleFiberPowerGeneration

noncomputable section

/-! Ampleness of an actual residue fiber constructs a positive power
and global sections generating that power over an affine neighborhood. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

theorem properFlat_exists_power_generating_near_ample_fiber
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : S)
    (hL : (L.pullback (f.fiberι x)).IsAmple) :
    ∃ (d : ℕ) (_ : 0 < d) (n : ℕ)
      (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf))
      (U : S.Opens), x ∈ U ∧ IsAffineOpen U ∧
        ∀ y : (f ⁻¹ᵁ U).toScheme, ∃ i, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
          (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ⁻¹ᵁ U).ι (s i)) := by
  have : IsProper (f.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd f (S.fromSpecResidueField x) inferInstance
  obtain ⟨d, hd, n, t, ht, hv⟩ := AmpleAllVanishing.ample_exists_power_sections_and_vanishing
    (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)) hL
  let e := L.powerBaseChangeIso (f.fiberι x) d
  have : Subsingleton (SheafCohomology.AffineH.Projective.H ((L.pullback (f.fiberι x)).tensorPower d).sheaf 1) := hv 1 (by decide)
  have : Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback (f.fiberι x)).obj
      (L.tensorPower d).sheaf) 1) :=
    (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor (f.fiber x) 1).map e.hom)).injective.subsingleton
  have hg : ∀ y : f.fiber x, ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f.fiber x) ⟶
      ((L.tensorPower d).pullback (f.fiberι x)).sheaf, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
    intro y
    obtain ⟨i, hi⟩ := ht y
    exact ⟨t i ≫ e.inv, (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (t i) e.symm).symm ▸ hi⟩
  obtain ⟨m, s, U, hxU, hU, hs⟩ :=
    Proper.FlatGenerationNeighborhood.properFlat_exists_generating_sections_near_fiber f (L.tensorPower d) x hg
  exact ⟨d, hd, m, s, U, hxU, hU, hs⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleFiberPowerGeneration
