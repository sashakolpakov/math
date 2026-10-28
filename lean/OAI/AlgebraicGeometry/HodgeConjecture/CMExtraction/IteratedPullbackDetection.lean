import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection

/-! # Iterated Pullback Detection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IteratedPullbackDetection.IsogenyQuotient

noncomputable section

/-! Maps into an iterated abelian-family pullback are determined by their
projection to the original family. The structural base map is already fixed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S Q T : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (s : Q ⟶ S) (b : T ⟶ Q) {Z : Over T}

theorem iterated_pullback_hom_ext
    (f k : Z ⟶ ((A.pullback s).pullback b).scheme)
    (h : f.left ≫ pullback.fst (pullback.snd A.scheme.hom s) b ≫ pullback.fst A.scheme.hom s =
      k.left ≫ pullback.fst (pullback.snd A.scheme.hom s) b ≫ pullback.fst A.scheme.hom s) : f = k := by
  let e := A.pullbackCompIso s b
  have hp : e.inv.left ≫ pullback.fst A.scheme.hom (b ≫ s) =
      pullback.fst (pullback.snd A.scheme.hom s) b ≫ pullback.fst A.scheme.hom s := by
    change (A.pullbackCompIso s b).inv.left ≫ _ = _
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    exact HeckeCycles.Source.SquareProjection.CM.pullbackComp_inv_projection b s A.scheme
  apply (cancel_mono e.inv).mp
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (f.left ≫ e.inv.left) ≫ pullback.fst A.scheme.hom (b ≫ s) =
      (k.left ≫ e.inv.left) ≫ pullback.fst A.scheme.hom (b ≫ s)
    exact ((Category.assoc _ _ _).trans (congrArg (fun d => f.left ≫ d) hp)).trans
      (h.trans ((congrArg (fun d => k.left ≫ d) hp).symm.trans (Category.assoc _ _ _).symm))
  · exact (f ≫ e.inv).w.trans (k ≫ e.inv).w.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IteratedPullbackDetection.IsogenyQuotient
