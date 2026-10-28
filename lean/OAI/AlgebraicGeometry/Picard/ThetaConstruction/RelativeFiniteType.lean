import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroScheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctorCharts

/-! # Relative Finite Type -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! Local finite type and quasi-compactness of the actual global
zero scheme descend from its normalized-frame charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctorCharts.Construction

variable {S : Scheme} {A B : Over S} [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsLocallyNoetherian B.left] (PP : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

theorem zeroScheme_localProperty (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ (T : Over S) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [IsLocallyNoetherian T.left]
      (a : T ⟶ B), P (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart PP D a).hom) : P (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom := by
  have := RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeSubfunctor_isRepresentable D PP
  let U := B.left.affineCover
  let T := fun i : U.I₀ => Over.mk (U.f i ≫ B.hom)
  let a := fun i : U.I₀ => (Over.homMk (U.f i) rfl : T i ⟶ B)
  let (i : U.I₀) : IsAffine (T i).left := inferInstanceAs (IsAffine (B.left.affineCover.X i))
  let (i : U.I₀) : IsLocallyNoetherian (T i).left := LocallyOfFiniteType.isLocallyNoetherian (U.f i)
  let (i : U.I₀) : IsNoetherianRing Γ((T i).left, ⊤) := by
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U.X i)⟩
  let M := fun i => RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart PP D (a i)
  let (i : U.I₀) : Mono (M i).hom := RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart_mono PP D (a i)
  exact FormalGeometry.Completion.RepresentedSubfunctorCharts.Construction.representedSubfunctor_localProperty (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeSubfunctor D) U M
    (fun i Z j => RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroChart_schemeFactorization D PP (a i) Z j) P (fun i => hP (T i) (a i))

instance zeroScheme_locallyOfFiniteType : LocallyOfFiniteType (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom := by
  have hlocal : IsZariskiLocalAtTarget (@AlgebraicGeometry.LocallyOfFiniteType.{0}) :=
    (HasAffineProperty.iff.mp
      (HasRingHomProperty.HasAffineProperty (@AlgebraicGeometry.LocallyOfFiniteType.{0}))).1
  exact @zeroScheme_localProperty S A B _ _ _ _ _ PP D
    (@AlgebraicGeometry.LocallyOfFiniteType.{0}) hlocal
    (fun _ _ _ _ a => RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart_locallyOfFiniteType PP D a)

instance zeroScheme_quasiCompact : QuasiCompact (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom := by
  have haff : HasAffineProperty (@AlgebraicGeometry.QuasiCompact.{0})
      (fun X _ _ _ => CompactSpace X) := by
    exact {
      eq_targetAffineLocally' := by
        ext X Y f
        simp only [quasiCompact_iff_forall_isAffineOpen, isCompact_iff_compactSpace,
          targetAffineLocally, Subtype.forall]
        rfl
      isLocal_affineProperty := by
        constructor
        · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
          exacts [@Homeomorph.compactSpace _ _ _ _ H (TopCat.homeoOfIso (asIso e.inv.base)), H]
        · introv _ H
          rw [Scheme.preimage_basicOpen f r]
          exact isCompact_iff_compactSpace.mp (isCompact_basicOpen _ isCompact_univ _)
        · rintro X Y H f S hS hS'
          rw [← (isAffineOpen_top _).iSup_basicOpen_eq_self_iff] at hS
          rw [← isCompact_univ_iff, ← TopologicalSpace.Opens.coe_top, ← f.preimage_top,
            ← hS, Scheme.Hom.preimage_iSup, TopologicalSpace.Opens.iSup_mk,
            TopologicalSpace.Opens.coe_mk]
          exact isCompact_iUnion fun i => isCompact_iff_compactSpace.mpr (hS' i) }
  have hlocal := (HasAffineProperty.iff.mp haff).1
  exact @zeroScheme_localProperty S A B _ _ _ _ _ PP D
    (@AlgebraicGeometry.QuasiCompact.{0}) hlocal
    (fun _ _ _ _ a => RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart_quasiCompact PP D a)

instance zeroInclusion_mono : Mono (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D PP) :=
  inferInstanceAs (Mono (FormalGeometry.Completion.FamilyLiftFactorization.Construction.compositeFamilyMap B (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP)))

instance zeroInclusion_left_mono : Mono (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D PP).left :=
  inferInstanceAs (Mono (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom)

instance zeroInclusion_left_quasiCompact : QuasiCompact (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D PP).left :=
  inferInstanceAs (QuasiCompact (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom)

instance zeroSchemeOver_locallyOfFiniteType [LocallyOfFiniteType B.hom] :
    LocallyOfFiniteType (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver D PP).hom := by
  change LocallyOfFiniteType ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom ≫ B.hom)
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts
