import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatAmpleDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatAmpleNeighborhood

/-! # Geometric Ample Neighborhood -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAmpleNeighborhood

noncomputable section

/-! Ampleness on a geometric coefficient fiber descends to the actual
residue fiber and extends to an affine neighborhood of its base point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem proper_isAmple_of_field_baseChange
    {k K : Type} [Field k] [Field K] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (a : Y ⟶ X) (ρ : Y ⟶ Spec (.of K)) (g : Spec (.of K) ⟶ Spec (.of k))
    (hp : IsPullback a ρ f g) (hL : (L.pullback a).IsAmple) : L.IsAmple :=
  FlatAmpleDescent.properFlat_isAmple_of_flat_surjective_baseChange f L a ρ g hp g.flat_appTop hL

theorem properFlat_exists_affine_ample_neighborhood_of_geometric_fiber
    {X Y S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {K : Type} [Field K] (a : Y ⟶ X) (ρ : Y ⟶ Spec (.of K)) (g : Spec (.of K) ⟶ S)
    (hp : IsPullback a ρ f g) (hL : (L.pullback a).IsAmple) :
    ∃ U : S.Opens, g (IsLocalRing.closedPoint K) ∈ U ∧ IsAffineOpen U ∧
      (L.pullback (f ⁻¹ᵁ U).ι).IsAmple := by
  let x := g (IsLocalRing.closedPoint K)
  let k : Spec (.of K) ⟶ Spec (S.residueField x) :=
    Spec.map (S.descResidueField (Scheme.stalkClosedPointTo g))
  have hk : k ≫ S.fromSpecResidueField x = g :=
    S.descResidueField_stalkClosedPointTo_fromSpecResidueField K g
  let b : Y ⟶ f.fiber x := pullback.lift a (ρ ≫ k) (by rw [Category.assoc, hk]; exact hp.w)
  have hb : b ≫ f.fiberι x = a := pullback.lift_fst _ _ _
  have hw : b ≫ f.fiberToSpecResidueField x = ρ ≫ k := pullback.lift_snd _ _ _
  have hout : IsPullback (b ≫ f.fiberι x) ρ f (k ≫ S.fromSpecResidueField x) := by
    rw [hb, hk]
    exact hp
  have hpb : IsPullback b ρ (f.fiberToSpecResidueField x) k :=
    hout.of_right hw (IsPullback.of_hasPullback f (S.fromSpecResidueField x))
  have : IsProper (f.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd f (S.fromSpecResidueField x) inferInstance
  let e : ((L.pullback (f.fiberι x)).pullback b).sheaf ≅ (L.pullback a).sheaf :=
    (Scheme.Modules.pullbackComp b (f.fiberι x)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hb).app L.sheaf
  have hF : (L.pullback (f.fiberι x)).IsAmple :=
    proper_isAmple_of_field_baseChange (f.fiberToSpecResidueField x)
      (L.pullback (f.fiberι x)) b ρ k hpb (hL.of_iso e.symm)
  exact Proper.FlatAmpleNeighborhood.properFlat_exists_affine_ample_neighborhood f L x hF

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAmpleNeighborhood
