import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AtIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelScheme

/-! # Translation Kernel Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelComparison

noncomputable section

/-! Actual Poincare recovery identifies the original translation kernel
with the kernel of its inducing isogeny, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric

local instance (X : Scheme.{0}) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

variable {S : Scheme.{0}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.poincareAt_relative_zero_iff
    (D : Dual.Data.DualAbelianData A) {T : Over S} (a : T ⟶ D.abelian.scheme) :
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf (D.poincareAt a)) =
      Picard.PicardSheaf.trivialPicardClass A.scheme T ↔ a = 1 := by
  have hz : (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
      (Line.Bundles.LineBundle.classOf (D.poincareAt (1 : T ⟶ D.abelian.scheme))) =
        Picard.PicardSheaf.trivialPicardClass A.scheme T :=
    congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T))
      (Quotient.sound ⟨D.poincareAt_oneIso T⟩)
  constructor
  · intro ha
    apply D.representable.homEquiv.injective
    apply A.homogeneousPicardSectionInclusion_injective T
    exact (D.pointRelativeClass_eq_poincare a).trans
      (ha.trans ((D.pointRelativeClass_eq_poincare 1).trans hz).symm)
  · rintro rfl
    exact hz

theorem relativeDifference_zero_iff_inducing_zero
    (D : Dual.Data.DualAbelianData A) (m : A.scheme ⟶ D.abelian.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left)
    (recover : Line.Bundles.LineBundle.classOf (D.poincareAt m) =
      Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))
    {T : Over S} (a : T ⟶ A.scheme) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = Picard.PicardSheaf.trivialPicardClass A.scheme T ↔
      a ≫ m = 1 := by
  have hvalue : (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
      (Line.Bundles.LineBundle.classOf (D.poincareAt (a ≫ m))) =
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a := by
    apply congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T))
    change Line.Bundles.LineBundle.pullbackClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map (a ≫ m))
      (Line.Bundles.LineBundle.classOf D.poincare) =
        Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 A.scheme).left
          (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))
    rw [tensorHom_id, Functor.map_comp, Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (Line.Bundles.LineBundle.pullbackClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map a)) recover
  rw [← hvalue]
  exact D.poincareAt_relative_zero_iff (a ≫ m)

variable [IsLocallyNoetherian S]

local instance comparison_abelian_locallyNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

theorem translationKernel_iso_of_poincare_class
    (D : Dual.Data.DualAbelianData A) (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (L : Line.Bundles.LineBundle A.scheme.left) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (recover : Line.Bundles.LineBundle.classOf (D.poincareAt m.hom) =
      Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) :
    ∃ e : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P ≅ m.kernelScheme,
      e.hom ≫ m.kernelInclusion = Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  have : Mono i := Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  have : Mono m.kernelInclusion := Over.mono_of_mono_left _
  have hi : i ≫ m.hom = 1 :=
    (relativeDifference_zero_iff_inducing_zero D m.hom L recover i).mp
      (Picard.ThetaConstruction.RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.zeroInclusion_relative_zero (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P)
  let a : m.kernelAt Z := ⟨i, hi⟩
  let q := (m.kernelSchemePointsEquiv Z).symm a
  have hq : q ≫ m.kernelInclusion = i :=
    congrArg Subtype.val ((m.kernelSchemePointsEquiv Z).apply_symm_apply a)
  have hk : (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue m.kernelInclusion =
      Picard.PicardSheaf.trivialPicardClass A.scheme m.kernelScheme :=
    (relativeDifference_zero_iff_inducing_zero D m.hom L recover m.kernelInclusion).mpr
      m.kernelInclusion_comp
  obtain ⟨r, hr⟩ :=
    (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization A L P m.kernelScheme m.kernelInclusion).mp hk
  refine ⟨⟨q, r, ?_, ?_⟩, hq⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hr, hq, Category.id_comp]
  · apply (cancel_mono m.kernelInclusion).mp
    rw [Category.assoc, hq, hr, Category.id_comp]

omit [IsLocallyNoetherian S] in
theorem relativeDifference_class_eq_of_lineClass
    (L M : Line.Bundles.LineBundle A.scheme.left) (hLM : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M) :
    Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) =
      Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A M) := by
  have hn : Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L) =
      Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A M) := by
    change Line.Bundles.LineBundle.classOf L *
        (Line.Bundles.LineBundle.pullbackClass A.scheme.hom
          (Line.Bundles.LineBundle.pullbackClass η[A.scheme].left (Line.Bundles.LineBundle.classOf L)))⁻¹ =
      Line.Bundles.LineBundle.classOf M *
        (Line.Bundles.LineBundle.pullbackClass A.scheme.hom
          (Line.Bundles.LineBundle.pullbackClass η[A.scheme].left (Line.Bundles.LineBundle.classOf M)))⁻¹
    rw [hLM]
  change Line.Bundles.LineBundle.pullbackClass μ[A.scheme].left (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) *
      (Line.Bundles.LineBundle.pullbackClass (fst A.scheme A.scheme).left
        (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)))⁻¹ *
      (Line.Bundles.LineBundle.pullbackClass (snd A.scheme A.scheme).left
        (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)))⁻¹ =
    Line.Bundles.LineBundle.pullbackClass μ[A.scheme].left (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A M)) *
      (Line.Bundles.LineBundle.pullbackClass (fst A.scheme A.scheme).left
        (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A M)))⁻¹ *
      (Line.Bundles.LineBundle.pullbackClass (snd A.scheme A.scheme).left
        (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A M)))⁻¹
  rw [hn]

omit [IsLocallyNoetherian S] in
theorem relativeDifference_value_eq_of_lineClass
    (L M : Line.Bundles.LineBundle A.scheme.left) (hLM : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M)
    {T : Over S} (a : T ⟶ A.scheme) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A M).relativeValue a := by
  exact congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T))
    (congrArg (Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 A.scheme).left)
      (relativeDifference_class_eq_of_lineClass L M hLM))

theorem translationKernel_iso_of_lineClass
    (L M : Line.Bundles.LineBundle A.scheme.left) (P Q : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hLM : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M) :
    ∃ e : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P ≅ Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A M Q,
      e.hom ≫ Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A M Q = Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P := by
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let j := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A M Q
  have : Mono i := Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  have : Mono j := Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono Q (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A M)
  have hi : (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A M).relativeValue i =
      Picard.PicardSheaf.trivialPicardClass A.scheme (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :=
    (relativeDifference_value_eq_of_lineClass L M hLM i).symm.trans
      (Picard.ThetaConstruction.RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.zeroInclusion_relative_zero (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P)
  have hj : (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue j =
      Picard.PicardSheaf.trivialPicardClass A.scheme (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A M Q) :=
    (relativeDifference_value_eq_of_lineClass L M hLM j).trans
      (Picard.ThetaConstruction.RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.zeroInclusion_relative_zero (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A M) Q)
  obtain ⟨a, ha⟩ := (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization A M Q _ i).mp hi
  obtain ⟨b, hb⟩ := (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization A L P _ j).mp hj
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hb, ha, Category.id_comp]
  · apply (cancel_mono j).mp
    rw [Category.assoc, ha, hb, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelComparison
