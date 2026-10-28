import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FiberIsomorphism

/-! # Fiber Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberIsomorphism

noncomputable section

/-! Fibers at ground-field rational points are the actual residue fibers after the canonical coefficient-field isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {S X P : Scheme.{u}}
    (p : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S) (hs : s ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ Spec (.of K)} {f : X ⟶ S}

def rationalFiberMap (p : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S)
    (hs : s ≫ p = 𝟙 _) (f : X ⟶ S) :
    pullback f s ⟶ f.fiber (s (IsLocalRing.closedPoint K)) :=
  pullback.map f s f (S.fromSpecResidueField (s (IsLocalRing.closedPoint K)))
    (𝟙 X) (Spec.map (PointResidue.rationalPointResidueIso p s hs).hom) (𝟙 S)
    (by simp) ((Category.comp_id s).trans (PointResidue.rationalPointResidueIso_factor p s hs).symm)

theorem rationalFiberMap_isIso (f : X ⟶ S) : IsIso (rationalFiberMap p s hs f) := by
  have : IsIso (Spec.map (PointResidue.rationalPointResidueIso p s hs).hom) := inferInstance
  exact pullback.map_isIso f s f (S.fromSpecResidueField (s (IsLocalRing.closedPoint K)))
    (𝟙 X) (Spec.map (PointResidue.rationalPointResidueIso p s hs).hom) (𝟙 S)
    (by simp) ((Category.comp_id s).trans (PointResidue.rationalPointResidueIso_factor p s hs).symm)

def rationalFiberIso (p : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S)
    (hs : s ≫ p = 𝟙 _) (H : IsPullback a b f s) :
    P ≅ f.fiber (s (IsLocalRing.closedPoint K)) :=
  H.isoPullback ≪≫ @asIso Scheme _ (pullback f s) (f.fiber (s (IsLocalRing.closedPoint K)))
    (rationalFiberMap p s hs f) (rationalFiberMap_isIso p s hs f)

@[reassoc]
theorem rationalFiberIso_fiberι (H : IsPullback a b f s) :
    (rationalFiberIso p s hs H).hom ≫ f.fiberι (s (IsLocalRing.closedPoint K)) = a := by
  have h : rationalFiberMap p s hs f ≫ f.fiberι (s (IsLocalRing.closedPoint K)) =
      pullback.fst f s := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  change (H.isoPullback.hom ≫ rationalFiberMap p s hs f) ≫ f.fiberι _ = a
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => H.isoPullback.hom ≫ t) h).trans H.isoPullback_hom_fst)

@[reassoc]
theorem rationalFiberIso_structure (H : IsPullback a b f s) :
    (rationalFiberIso p s hs H).hom ≫ f.fiberToSpecResidueField (s (IsLocalRing.closedPoint K)) =
      b ≫ Spec.map (PointResidue.rationalPointResidueIso p s hs).hom := by
  have h : rationalFiberMap p s hs f ≫ f.fiberToSpecResidueField (s (IsLocalRing.closedPoint K)) =
      pullback.snd f s ≫ Spec.map (PointResidue.rationalPointResidueIso p s hs).hom := pullback.lift_snd _ _ _
  change (H.isoPullback.hom ≫ rationalFiberMap p s hs f) ≫ f.fiberToSpecResidueField _ = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => H.isoPullback.hom ≫ t) h).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ Spec.map (PointResidue.rationalPointResidueIso p s hs).hom) H.isoPullback_hom_snd)))

def rationalFiberBundleIso (H : IsPullback a b f s) (L : Line.Bundles.LineBundle X) :
    ((L.pullback (f.fiberι (s (IsLocalRing.closedPoint K)))).pullback
      (rationalFiberIso p s hs H).hom).sheaf ≅ (L.pullback a).sheaf :=
  (Scheme.Modules.pullbackComp (rationalFiberIso p s hs H).hom
    (f.fiberι (s (IsLocalRing.closedPoint K)))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (rationalFiberIso_fiberι p s hs H)).app L.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberIsomorphism
