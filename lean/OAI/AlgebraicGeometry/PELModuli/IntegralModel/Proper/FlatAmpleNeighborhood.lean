import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleFiberPowerGeneration
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.SectionAmpleness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.CartesianRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ImageAmpleness

/-! # Flat Ample Neighborhood -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatAmpleNeighborhood

noncomputable section

/-! Ampleness on one residue fiber of a proper flat family extends to
an actual affine base neighborhood. All generating sections are constructed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.SectionAmpleness.PolarizationEmbedding

theorem properFlat_exists_affine_ample_neighborhood
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : S)
    (hL : (L.pullback (f.fiberι x)).IsAmple) :
    ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧
      (L.pullback (f ⁻¹ᵁ U).ι).IsAmple := by
  obtain ⟨d, hd, n, s, U, hxU, hU, hs⟩ :=
    AmpleFiberPowerGeneration.properFlat_exists_power_generating_near_ample_fiber f L x hL
  have : IsAffine U.toScheme := hU
  let P := L.tensorPower d
  let G := P.pullback (f ⁻¹ᵁ U).ι
  let sU := fun i => AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ⁻¹ᵁ U).ι (s i)
  have hr : Set.range (S.fromSpecResidueField x) ⊆ (U : Set S) := by
    rintro _ ⟨t, rfl⟩
    change S.fromSpecResidueField x t ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hxU
  obtain ⟨a, g, ha, hg, hp⟩ := Open.CartesianRestriction.exists_cartesian_open_lifts f (f.fiberι x)
    (f.fiberToSpecResidueField x) (S.fromSpecResidueField x)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) U hr
  let e : (G.pullback a).sheaf ≅ (P.pullback (f.fiberι x)).sheaf :=
    (Scheme.Modules.pullbackComp a (f ⁻¹ᵁ U).ι).app P.sheaf ≪≫
      (Scheme.Modules.pullbackCongr ha).app P.sheaf
  have hP : (P.pullback (f.fiberι x)).IsAmple :=
    (hL.tensorPower d hd).of_iso (L.powerBaseChangeIso (f.fiberι x) d).symm
  let t := IsLocalRing.closedPoint (S.residueField x)
  obtain ⟨V, htV, hV, hGV⟩ :=
    Cartesian.SectionAmpleness.PolarizationEmbedding.exists_affine_ample_neighborhood_of_cartesian_generated_ample (f ∣_ U) G sU hs
      a (f.fiberToSpecResidueField x) g hp t (hP.of_iso e.symm)
  let W := U.ι ''ᵁ V
  have hxW : x ∈ W := by
    refine ⟨g t, htV, ?_⟩
    have h := congrArg (fun z : Spec (S.residueField x) ⟶ S => z t) hg
    exact h.trans (S.fromSpecResidueField_apply x t)
  have hW : IsAffineOpen W := hV.image_of_isOpenImmersion U.ι
  have hPW : (P.pullback (f ⁻¹ᵁ W).ι).IsAmple := by
    have h := Open.ImageAmpleness.isAmple_on_open_image (f ⁻¹ᵁ U).ι P ((f ∣_ U) ⁻¹ᵁ V) hGV
    rwa [image_morphismRestrict_preimage] at h
  exact ⟨W, hxW, hW, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsAmple.of_tensorPower d hd
    (hPW.of_iso (L.powerBaseChangeIso (f ⁻¹ᵁ W).ι d))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatAmpleNeighborhood
