import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

/-! # Pullback Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PullbackRetraction

noncomputable section

/-! The actual polarized full-level pullback returns to the original
object along a retraction of bases, with its precise carrier comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

theorem abelianPullbackCongrIso_hom (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f h : T ⟶ S) (w : f = h) :
    (A.pullbackCongrIso f h w).hom =
      (eqToIso (congrArg (fun q : T ⟶ S => Over.pullback q) w)).hom.app A.scheme := by
  subst h
  rfl

theorem purePullbackCongrIso_dual (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f h : T ⟶ S) (w : f = h) :
    (Pure.RelativeLevelIso.purePullbackCongrIso A f h w).dual = A.dual.abelian.pullbackCongrIso f h w := by
  subst h
  rfl

def polarizedPullbackRetractionIso (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : T ⟶ S) (h : S ⟶ T) (w : h ≫ f = 𝟙 S) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback f).pullback h) A :=
  (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f h).trans
    ((Pure.RelativeLevelIso.purePullbackCongrIso A (h ≫ f) (𝟙 S) w).trans (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A))

theorem polarizedPullbackRetractionIso_abelian (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : T ⟶ S) (h : S ⟶ T) (w : h ≫ f = 𝟙 S) :
    (polarizedPullbackRetractionIso A f h w).abelian.hom =
      (((Over.pullbackComp h f).symm ≪≫
        eqToIso (congrArg (fun q : S ⟶ S => Over.pullback q) w) ≪≫ Over.pullbackId).hom.app A.abelian.scheme) := by
  change (A.abelian.pullbackCompIso f h).inv ≫
    (Pure.RelativeLevelIso.purePullbackCongrIso A (h ≫ f) (𝟙 S) w).abelian.hom ≫ A.abelian.pullbackIdIso.hom = _
  rw [Pure.RelativeLevelIso.purePullbackCongrIso_abelian, abelianPullbackCongrIso_hom,
    HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv, HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
  rfl

theorem polarizedPullbackRetractionIso_dual (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : T ⟶ S) (h : S ⟶ T) (w : h ≫ f = 𝟙 S) :
    (polarizedPullbackRetractionIso A f h w).dual.hom =
      (((Over.pullbackComp h f).symm ≪≫
        eqToIso (congrArg (fun q : S ⟶ S => Over.pullback q) w) ≪≫ Over.pullbackId).hom.app A.dual.abelian.scheme) := by
  change (A.dual.abelian.pullbackCompIso f h).inv ≫
    (Pure.RelativeLevelIso.purePullbackCongrIso A (h ≫ f) (𝟙 S) w).dual.hom ≫ A.dual.abelian.pullbackIdIso.hom = _
  rw [purePullbackCongrIso_dual, abelianPullbackCongrIso_hom,
    HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv, HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PullbackRetraction
