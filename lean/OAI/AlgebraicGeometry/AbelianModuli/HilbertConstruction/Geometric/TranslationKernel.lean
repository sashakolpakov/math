import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceGroup
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalDifferenceHomogeneity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Finite
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KilledGroupEtale
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit

/-! # Translation Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.TranslationKernel

noncomputable section

/-! The represented translation kernel of an ample line is finite over
an algebraically closed field, and is etale in characteristic zero.
The comparison retains the actual all-test Picard-zero functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

local instance geometricKernelPicardCommGroup (X : Scheme) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

theorem identityNormalizedLine_field_class
    {k : Type} [Field k] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (L : Line.Bundles.LineBundle A.scheme.left) :
    Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L) = Line.Bundles.LineBundle.classOf L := by
  have hz : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback η[A.scheme].left (Line.Bundles.LineBundle.classOf L) = 1 :=
    Quotient.sound (RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality.lineBundle_over_field_trivial k (L.pullback η[A.scheme].left))
  change Line.Bundles.LineBundle.classOf L *
    (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback A.scheme.hom (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback η[A.scheme].left (Line.Bundles.LineBundle.classOf L)))⁻¹ = _
  rw [hz, map_one, inv_one, mul_one]

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : Line.Bundles.LineBundle A.scheme.left)

local instance geometricKernel_geometricallyIntegral : GeometricallyIntegral A.scheme.hom :=
  FormalGeometry.Completion.SmoothGeometricIntegrality.Construction.proper_smooth_geometricallyIntegral_of_geometricallyConnected A.scheme.hom

theorem geometricDifference_value_eq_polarization
    {T : Over (Spec (.of k))} (a : T ⟶ A.scheme) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      FormalGeometry.Completion.Polarization.PicardMap.Construction.polarizationRelativeSection A.scheme L a := by
  apply congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (op T))
  change RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a =
    (FormalGeometry.Completion.Polarization.Family.Construction.polarizationFamilyClass A.scheme L a).toMul
  rw [Picard.ThetaConstruction.ReducedLocalDifferenceHomogeneity.Geometric.relativeDifference_parameter_class, identityNormalizedLine_field_class]
  have hd (r : Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
      Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dualClass r = r⁻¹ :=
    eq_inv_of_mul_eq_one_left (Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation.dual_tensorClass r)
  rw [FormalGeometry.Completion.Polarization.Family.Construction.polarizationFamilyClass, FormalGeometry.Completion.SchemePointPicardPairing.Construction.schemePointPicardPairing_apply]
  dsimp only [FormalGeometry.Completion.SchemePointPicardPairing.Construction.schemePointLineBundleClass, Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value,
    Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map, RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback]
  let x := Line.Bundles.LineBundle.pullbackClass ((fst T A.scheme ≫ a) * snd T A.scheme).left (Line.Bundles.LineBundle.classOf L)
  let y := Line.Bundles.LineBundle.pullbackClass (fst T A.scheme ≫ a).left (Line.Bundles.LineBundle.classOf L)
  let z := Line.Bundles.LineBundle.pullbackClass (snd T A.scheme).left (Line.Bundles.LineBundle.classOf L)
  change x * y⁻¹ * z⁻¹ =
    Line.Bundles.LineBundle.tensorClass (Line.Bundles.LineBundle.tensorClass x (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dualClass y))
      (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dualClass z)
  rw [hd, hd]
  rfl

variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance geometricKernel_locallyNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

theorem geometricDifference_polarizationKernel_iso :
    ∃ e : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P ≅ FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelOver A.scheme L,
      e.hom ≫ FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelInclusion A.scheme L = Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let K := FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelOver A.scheme L
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let j := FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelInclusion A.scheme L
  let : Mono i := Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  let : Mono j := inferInstanceAs (Mono (FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelInclusion A.scheme L))
  have hK (T : Over (Spec (.of k))) (a : T ⟶ A.scheme) :
      FormalGeometry.Completion.Polarization.PicardMap.Construction.polarizationRelativeSection A.scheme L a = Picard.PicardSheaf.trivialPicardClass A.scheme T ↔
        ∃ f : T ⟶ K, f ≫ j = a := by
    exact FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelOver_factorization A.scheme L T a
  have hi : FormalGeometry.Completion.Polarization.PicardMap.Construction.polarizationRelativeSection A.scheme L i = Picard.PicardSheaf.trivialPicardClass A.scheme Z :=
    (geometricDifference_value_eq_polarization A L i).symm.trans
      (Picard.ThetaConstruction.RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.zeroInclusion_relative_zero (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P)
  obtain ⟨f, hf⟩ := (hK Z i).mp hi
  have hj : (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue j = Picard.PicardSheaf.trivialPicardClass A.scheme K :=
    (geometricDifference_value_eq_polarization A L j).trans
      (FormalGeometry.Completion.PolarizationKernel.Finite.Construction.polarizationKernelInclusion_relative_zero A.scheme L)
  obtain ⟨h, hh⟩ := (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization A L P K j).mp hj
  refine ⟨⟨f, h, ?_, ?_⟩, hf⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hh, hf, Category.id_comp]
  · apply (cancel_mono j).mp
    rw [Category.assoc, hf, hh, Category.id_comp]

theorem geometricTranslationKernel_isFinite (hL : L.IsAmple) :
    IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  obtain ⟨e, _⟩ := geometricDifference_polarizationKernel_iso A L P
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map e.hom))
  let : IsFinite (FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelOver A.scheme L).hom := FormalGeometry.Completion.PolarizationKernel.Finite.Construction.polarizationKernel_finite A.scheme L hL
  have h : IsFinite (e.hom.left ≫ (FormalGeometry.Completion.PolarizationKernel.OverRepresentation.Construction.polarizationKernelOver A.scheme L).hom) := inferInstance
  exact e.hom.w ▸ h

theorem geometricTranslationKernel_etale [CharZero k] (hL : L.IsAmple) :
    Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let : GrpObj Z := (Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup A L P).group
  let : IsCommMonObj Z := Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup_commutative A L P
  let : IsFinite Z.hom := geometricTranslationKernel_isFinite A L P hL
  obtain ⟨n, hn, hkill⟩ := FormalGeometry.Completion.Finite.GroupAnnihilator.Construction.finiteGroup_exists_annihilator k (Grp.mk Z)
  exact AbelianScheme.IsogenyQuotient.KilledGroupEtale.Construction.flatGroup_etale_of_killed Z n
    (AbelianScheme.IsogenyQuotient.Unit.Construction.positive_integer_unit_on_characteristic_zero_base (𝟙 (Spec (.of k))) n hn)
    (hkill Z (𝟙 Z))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.TranslationKernel
