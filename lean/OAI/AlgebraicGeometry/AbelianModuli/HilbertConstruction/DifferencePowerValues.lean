import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.DifferenceHomomorphism
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes

/-! # Difference Power Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferencePowerValues.Theta.Geometric

noncomputable section

/-! Tensor powers of the original line and powers of the parameter
give the same actual relative difference value. The identities hold
on all tests over a locally Noetherian projective base, in every
characteristic, and commute with the original base-change comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

local instance differencePowerPicardCommGroup (X : Scheme.{0}) :
    CommGroup (Line.Bundles.LineBundle.IsoClass X) := Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

private theorem mapped_difference_pow
    {G H : Type*} [CommGroup G] [CommGroup H]
    (p : G →* H) (t : G →* G) (q : G) (m : ℕ) :
    p (t (q ^ m)) * (p (q ^ m))⁻¹ = (p (t q) * (p q)⁻¹) ^ m := by
  simp only [map_pow, mul_pow, inv_pow]

variable {S : Scheme.{0}} {g : ℕ}

theorem relativeDifference_tensorPower_value
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    {T : Over S} (a : T ⟶ A.scheme) (m : ℕ) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A (L.tensorPower m)).relativeValue a =
      ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a) ^ m := by
  let q := Line.Bundles.LineBundle.classOf (L.pullback (snd T A.scheme).left)
  let p : Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left →* Picard.PicardSheaf.PicardSections A.scheme T :=
    Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T
  let t : Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left →*
      Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left
  have hq : Line.Bundles.LineBundle.classOf ((L.tensorPower m).pullback (snd T A.scheme).left) =
      q ^ m := by
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd T A.scheme).left (Line.Bundles.LineBundle.classOf (L.tensorPower m)) = _
    rw [Line.Bundles.LineBundle.classOf_tensorPower, map_pow]
    rfl
  have hpower := Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric.relativeDifference_value_original A (L.tensorPower m) a
  have hline := Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric.relativeDifference_value_original A L a
  change (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A (L.tensorPower m)).relativeValue a =
    p (t (Line.Bundles.LineBundle.classOf ((L.tensorPower m).pullback (snd T A.scheme).left))) *
      (p (Line.Bundles.LineBundle.classOf ((L.tensorPower m).pullback (snd T A.scheme).left)))⁻¹ at hpower
  change (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = p (t q) * (p q)⁻¹ at hline
  exact hpower.trans ((congrArg (fun r => p (t r) * (p r)⁻¹) hq).trans
    ((mapped_difference_pow p t q m).trans (congrArg (fun r => r ^ m) hline.symm)))

private def locallyNoetherianDifferenceLineHom
    (A : Abelian.Schemes.AbelianScheme g S) [IsLocallyNoetherian S]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left) (T : Over S) :
    (T ⟶ A.scheme) →* Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left where
  toFun := RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
  map_one' := by
    have h := LocallyNoetherian.DifferenceHomomorphism.Theta.Geometric.locallyNoetherian_parameterDifferenceLineClass_mul A P L
      (1 : T ⟶ A.scheme) 1
    rw [one_mul] at h
    exact (mul_left_cancel ((mul_one _).trans h)).symm
  map_mul' := LocallyNoetherian.DifferenceHomomorphism.Theta.Geometric.locallyNoetherian_parameterDifferenceLineClass_mul A P L

theorem locallyNoetherian_relativeDifference_value_pow
    (A : Abelian.Schemes.AbelianScheme g S) [IsLocallyNoetherian S]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    {T : Over S} (a : T ⟶ A.scheme) (m : ℕ) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (a ^ m) =
      ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a) ^ m := by
  let p := (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T).comp
    (locallyNoetherianDifferenceLineHom A P L T)
  exact p.map_pow a m

theorem relativeDifference_tensorPower_eq_parameter_pow
    (A : Abelian.Schemes.AbelianScheme g S) [IsLocallyNoetherian S]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    {T : Over S} (a : T ⟶ A.scheme) (m : ℕ) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A (L.tensorPower m)).relativeValue a =
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (a ^ m) :=
  (relativeDifference_tensorPower_value A L a m).trans
    (locallyNoetherian_relativeDifference_value_pow A P L a m).symm

theorem relativeDifference_tensorPower_represents
    (A : Abelian.Schemes.AbelianScheme g S) [IsLocallyNoetherian S]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    {T : Over S} (a : T ⟶ A.scheme) (m : ℕ) (q : Picard.PicardSheaf.PicardSections A.scheme T)
    (h : (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A (L.tensorPower m)).relativeValue a = q) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (a ^ m) = q :=
  (relativeDifference_tensorPower_eq_parameter_pow A P L a m).symm.trans h

theorem relativeDifference_tensorPower_value_baseChange
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left) {S' : Scheme.{0}} [IsLocallyNoetherian S']
    (f : S' ⟶ S) (T : Over S') (a : T ⟶ (A.pullback f).scheme) (m : ℕ) :
    Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f T
      ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f)
        ((L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)).tensorPower m)).relativeValue a) =
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (A.baseChangePointsEquiv f T (a ^ m)) :=
  (congrArg (Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f T)
    (relativeDifference_tensorPower_eq_parameter_pow (A.pullback f) (P.baseChange f)
      (L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)) a m)).trans
    (Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric.relativeDifference_value_baseChange A L f T (a ^ m))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferencePowerValues.Theta.Geometric
