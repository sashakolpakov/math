import OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernHomogeneity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTranslationClasses
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup

/-! # Same Chern Translation Stabilizer -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Equal native Chern pairings give the same translation stabilizer
on every actual test scheme, including nonreduced tests. This follows
from all-test homogeneity of the ratio in the original Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

section Relative
universe u
variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T : Over S}

theorem SameChernTranslationStabilizer.Geometric.translationInvariant_iff_of_invariant_ratio (a : T ⟶ A.scheme)
    (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (h : A.TranslationInvariant a (q * r⁻¹)) :
    A.TranslationInvariant a q ↔ A.TranslationInvariant a r := by
  let η := Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T
  let τ := Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left
  have hτ : τ (q * r⁻¹) = τ q * (τ r)⁻¹ :=
    (τ.map_mul q r⁻¹).trans (congrArg (fun z => τ q * z) (τ.map_inv r))
  have hη (x y : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
      η (x * y⁻¹) = η x * (η y)⁻¹ :=
    (η.map_mul x y⁻¹).trans (congrArg (fun z => η x * z) (η.map_inv y))
  have hh : η (τ q) * (η (τ r))⁻¹ = η q * (η r)⁻¹ := by
    change η (τ (q * r⁻¹)) = η (q * r⁻¹) at h
    exact (hη (τ q) (τ r)).symm.trans ((congrArg η hτ).symm.trans (h.trans (hη q r)))
  constructor
  · intro hq
    change η (τ q) = η q at hq
    change η (τ r) = η r
    apply inv_injective
    apply mul_left_cancel (a := η q)
    simpa only [hq] using hh
  · intro hr
    change η (τ r) = η r at hr
    change η (τ q) = η q
    apply mul_right_cancel (b := (η r)⁻¹)
    simpa only [hr] using hh

end Relative

section Field
variable {k : Type} [Field k] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

theorem SameChernTranslationStabilizer.Geometric.homogeneousRatio_translationInvariant_iff
    (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left)
    (h : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (q * r⁻¹))
    (T : Over (Spec (.of k))) (a : T ⟶ A.scheme) :
    A.TranslationInvariant a (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T q) ↔
      A.TranslationInvariant a (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T r) := by
  let π := Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd T A.scheme).left
  have hh := h.family A T T (𝟙 T) a
  have hm : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 T).op
      (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T (q * r⁻¹)) = AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T (q * r⁻¹) :=
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_id_apply (Opposite.op T) _
  rw [hm] at hh
  have hi : A.TranslationInvariant a (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T (q * r⁻¹)) := hh
  have he : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T (q * r⁻¹) =
      AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T q * (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A T r)⁻¹ :=
    (π.map_mul q r⁻¹).trans (congrArg (fun z => π q * z) (π.map_inv r))
  rw [he] at hi
  exact SameChernTranslationStabilizer.Geometric.translationInvariant_iff_of_invariant_ratio A a _ _ hi

end Field

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.sameIntegralPairing_translationInvariant_iff (hE : E.transpose = -E)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (h : ∀ l m : T.lattice,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
        AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian K (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m))
    (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : U ⟶ M.abelianScheme.scheme) :
    M.abelianScheme.TranslationInvariant a (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) ↔
      M.abelianScheme.TranslationInvariant a (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)) := by
  have hk : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Homomorphisms.LineBundleDual.Construction.lineBundleDual K) = (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹ :=
    eq_inv_of_mul_eq_one_left (Homomorphisms.LineBundleEvaluation.Construction.tensorClass_dual (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K))
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual K)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹ :=
    (Homomorphisms.SchemeGroup.Construction.lineBundleClass_mul L (Homomorphisms.LineBundleDual.Construction.lineBundleDual K)).symm.trans
      (congrArg (fun z => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * z) hk)
  have hh := M.sameIntegralPairing_ratio_homogeneous hE L K h
  have hh' := (congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass M.abelian.toOver.left =>
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass M.abelianScheme q) he).mp hh
  exact SameChernTranslationStabilizer.Geometric.homogeneousRatio_translationInvariant_iff M.abelianScheme _ _ hh' U a

theorem PeriodModel.Geometric.AlgebraicPeriodModel.sameIntegralPairing_translationStabilizer_eq (hE : E.transpose = -E)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (h : ∀ l m : T.lattice,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
        AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian K (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m))
    (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    RelativeTranslationClasses.Geometric.relativeTranslationStabilizer M.abelianScheme (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
      RelativeTranslationClasses.Geometric.relativeTranslationStabilizer M.abelianScheme (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)) := by
  ext a
  exact M.sameIntegralPairing_translationInvariant_iff hE L K h U a

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
