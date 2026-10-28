import OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonScheme
import OAI.RepresentationTheory.Theta.Geometric.RigidifiedParameterPullback

/-! # Parameter Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ParameterComparison

noncomputable section

/-! The scheme comparing a parameterized Picard family with an arbitrary
rigidified family carries its actual parameter and base maps. Its points
are precisely the parameter maps realizing that family's Picard class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A N T : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian (N ⊗ T).left]
    (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A N) (L : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A T)

def picardParameterComparison : Over (Spec (.of K)) :=
  ComparisonScheme.picardComparisonOver (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N T))
    (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N T))

def picardParameterInclusion : picardParameterComparison Q L ⟶ N ⊗ T :=
  ComparisonScheme.picardComparisonInclusion (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N T))
    (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N T))

instance picardParameterInclusion_mono : Mono (picardParameterInclusion Q L) :=
  inferInstanceAs (Mono (ComparisonScheme.picardComparisonInclusion
    (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N T)) (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N T))))

def picardParameterMap : picardParameterComparison Q L ⟶ N :=
  picardParameterInclusion Q L ≫ fst N T

def picardParameterProjection : picardParameterComparison Q L ⟶ T :=
  picardParameterInclusion Q L ≫ snd N T

instance picardParameterInclusion_left_locallyOfFiniteType :
    LocallyOfFiniteType (picardParameterInclusion Q L).left :=
  inferInstanceAs (LocallyOfFiniteType (ComparisonScheme.picardComparisonInclusion
    (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N T)) (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N T))).left)

instance picardParameterInclusion_left_quasiCompact :
    QuasiCompact (picardParameterInclusion Q L).left :=
  inferInstanceAs (QuasiCompact (ComparisonScheme.picardComparisonInclusion
    (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N T)) (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N T))).left)

instance picardParameterProjection_locallyOfFiniteType [LocallyOfFiniteType N.hom] :
    LocallyOfFiniteType (picardParameterProjection Q L).left := by
  have : LocallyOfFiniteType (snd N T).left :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd N.hom T.hom))
  change LocallyOfFiniteType ((picardParameterInclusion Q L).left ≫ (snd N T).left)
  infer_instance

instance picardParameterProjection_quasiCompact [QuasiCompact N.hom] :
    QuasiCompact (picardParameterProjection Q L).left := by
  have : QuasiCompact (snd N T).left :=
    inferInstanceAs (QuasiCompact (CategoryTheory.Limits.pullback.snd N.hom T.hom))
  change QuasiCompact ((picardParameterInclusion Q L).left ≫ (snd N T).left)
  infer_instance

theorem picardParameterComparison_value {U : Over (Spec (.of K))}
    (z : U ⟶ picardParameterComparison Q L) :
    Q.relativeValue (z ≫ picardParameterMap Q L) =
      L.relativeValue (z ≫ picardParameterProjection Q L) := by
  have h := ComparisonScheme.picardComparison_compares (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N T))
    (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N T)) z
  rw [RigidifiedParameterPullback.rigidifiedParameterPullback_relativeValue, RigidifiedParameterPullback.rigidifiedParameterPullback_relativeValue] at h
  exact (congrArg Q.relativeValue (Category.assoc z (picardParameterInclusion Q L) (fst N T)).symm).trans
    (h.trans (congrArg L.relativeValue (Category.assoc z (picardParameterInclusion Q L) (snd N T))))

theorem picardParameterComparison_factorization {U : Over (Spec (.of K))}
    (a : U ⟶ N) (t : U ⟶ T) :
    Q.relativeValue a = L.relativeValue t ↔
      ∃ z : U ⟶ picardParameterComparison Q L,
        z ≫ picardParameterMap Q L = a ∧ z ≫ picardParameterProjection Q L = t := by
  have h := ComparisonScheme.picardComparison_factorization (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N T))
    (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N T)) (lift a t)
  rw [RigidifiedParameterPullback.rigidifiedParameterPullback_relativeValue, RigidifiedParameterPullback.rigidifiedParameterPullback_relativeValue,
    lift_fst, lift_snd] at h
  constructor
  · intro he
    obtain ⟨z, hz⟩ := h.mp he
    refine ⟨z, ?_, ?_⟩
    · exact (Category.assoc z (picardParameterInclusion Q L) (fst N T)).symm.trans
        ((congrArg (· ≫ fst N T) hz).trans (lift_fst a t))
    · exact (Category.assoc z (picardParameterInclusion Q L) (snd N T)).symm.trans
        ((congrArg (· ≫ snd N T) hz).trans (lift_snd a t))
  · rintro ⟨z, ha, ht⟩
    have hv := picardParameterComparison_value Q L z
    rw [ha, ht] at hv
    exact hv

theorem picardParameterProjection_mono
    (hQ : ∀ U : Over (Spec (.of K)), Function.Injective (Q.relativeValue (T := U))) :
    Mono (picardParameterProjection Q L) := by
  constructor
  intro U f g hfg
  apply (cancel_mono (picardParameterInclusion Q L)).mp
  apply CartesianMonoidalCategory.hom_ext
  · have hvf := picardParameterComparison_value Q L f
    have hvg := picardParameterComparison_value Q L g
    have hp : f ≫ picardParameterMap Q L = g ≫ picardParameterMap Q L :=
      hQ U (hvf.trans ((congrArg L.relativeValue hfg).trans hvg.symm))
    exact (Category.assoc f (picardParameterInclusion Q L) (fst N T)).trans
      (hp.trans (Category.assoc g (picardParameterInclusion Q L) (fst N T)).symm)
  · exact (Category.assoc f (picardParameterInclusion Q L) (snd N T)).trans
      (hfg.trans (Category.assoc g (picardParameterInclusion Q L) (snd N T)).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ParameterComparison
