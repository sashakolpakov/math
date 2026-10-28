import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicTranslationKernel

/-! # Same Chern Difference Values -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernDifferenceValues.Geometric

noncomputable section

/-! Equal native Chern pairings give equal actual difference-line
values, not just equal kernels. The homogeneous ratio is invariant
under every translation in the original relative Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

local instance nativeLineClassCommGroup (X : Scheme) : CommGroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :=
  Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

theorem commutative_ratio_swap {G : Type*} [CommGroup G] (a b c d : G)
    (h : a * c⁻¹ = b * d⁻¹) : a * b⁻¹ = c * d⁻¹ := by
  apply mul_inv_eq_one.mp
  calc
    (a * b⁻¹) * (c * d⁻¹)⁻¹ = (a * c⁻¹) * (b * d⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_inv_rev, inv_inv]
      calc
        (a * b⁻¹) * (d * c⁻¹) = (a * d) * (b⁻¹ * c⁻¹) := mul_mul_mul_comm _ _ _ _
        _ = (a * d) * (c⁻¹ * b⁻¹) := congrArg (fun x : G => (a * d) * x) (mul_comm _ _)
        _ = (a * c⁻¹) * (d * b⁻¹) := (mul_mul_mul_comm _ _ _ _).symm
    _ = 1 := by rw [h, mul_inv_cancel]

private theorem mapped_difference_of_trivial_middle
    {M N : Type*} [CommGroup M] [CommGroup N] (f : M →* N) (a b c : M) (hb : f b = 1) :
    f (a * b⁻¹ * c⁻¹) = f a * (f c)⁻¹ := by
  simp only [map_mul, map_inv, hb, inv_one, mul_one]

theorem nativeDifference_picard_value {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) {U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a =
      (Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U)
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) *
      ((Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U) (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))⁻¹ := by
  let η := Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U
  have hb : η (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst U A.scheme).left
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) = 1 :=
    (AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality.baseBundle_relativePicardClass_trivial A.scheme U (L.pullback a.left)).trans
      (Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one A.scheme U)
  change η (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a) = _
  exact (congrArg η (RepresentationTheory.Theta.Geometric.DifferencePicardClasses.parameterDifference_class A L a)).trans
    (@mapped_difference_of_trivial_middle (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left)
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme U) (Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup _) inferInstance
      η _ _ _ hb)

private theorem mapped_ratio_invariance
    {M N P : Type*} [CommGroup M] [CommGroup N] [CommGroup P]
    (σ : M →* N) (τ : N →* N) (η : N →* P) (q r : M)
    (h : η (τ (σ (q * r⁻¹))) = η (σ (q * r⁻¹))) :
    η (τ (σ q)) * (η (τ (σ r)))⁻¹ = η (σ q) * (η (σ r))⁻¹ := by
  simpa only [map_mul, map_inv] using h

theorem nativeDifference_eq_of_homogeneous_ratio {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (h : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹))
    {U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A K) a := by
  let η := Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U
  let τ := Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left
  let q := AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  let r := AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)
  have hh := h.family A U U (𝟙 U) a
  have hid : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 U).op
      (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹)) =
      AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹) :=
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_id_apply (.op U) _
  have hh' : η (τ (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹))) =
      η (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹)) :=
    (congrArg (fun x : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left => η (τ x)) hid).symm.trans
      (hh.trans (congrArg η hid))
  have hr : η (τ q) * (η (τ r))⁻¹ = η q * (η r)⁻¹ :=
    @mapped_ratio_invariance (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left) (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme U)
      (Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup _) (Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup _) inferInstance
      (Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd U A.scheme).left) τ η
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K) hh'
  rw [nativeDifference_picard_value, nativeDifference_picard_value]
  exact commutative_ratio_swap _ _ _ _ hr

namespace AlgebraicPeriodModel
variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.sameIntegralPairing_difference_value_eq (hE : E.transpose = -E)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (h : ∀ l m : T.lattice,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
        AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian K (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m))
    {U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : U ⟶ M.abelianScheme.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L) a =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme K) a :=
  nativeDifference_eq_of_homogeneous_ratio M.abelianScheme L K
    (M.sameIntegralPairing_ratio_homogeneous hE L K h) a

end AlgebraicPeriodModel

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernDifferenceValues.Geometric
