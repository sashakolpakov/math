import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SquareExternalEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OppositeAmpleEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ShearIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassEulerIsomorphism
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange

/-! # Difference Twist Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceTwistEuler

noncomputable section

/-! Twisting the normalized difference bundle by its first ample factor
turns it, under an actual shear of the square, into an external tensor
product. Some positive tensor power has nonzero Euler characteristic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric

local instance differenceEulerClassCommGroup (X : Scheme) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Line.Bundles.LineBundle.isoClassCommGroup X

variable {k : Type} [Field k] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of k)))

def differenceTwistedLine (L M : Line.Bundles.LineBundle A.scheme.left) :
    Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left :=
  ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
    (M.pullback (snd A.scheme A.scheme).left)

theorem differenceTwistedLine_shear_class (L M : Line.Bundles.LineBundle A.scheme.left) :
    Line.Bundles.LineBundle.classOf (differenceTwistedLine A L M) =
      Line.Bundles.LineBundle.pullbackClass (Product.ShearIsomorphisms.productShearIso A.scheme 1).hom.left
        (Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.externalTensor A.scheme.hom A.scheme.hom
          L (L.reciprocalFrameBundle.tensor M))) := by
  let x := (fst A.scheme A.scheme).left
  let y := (snd A.scheme A.scheme).left
  let z := μ[A.scheme].left
  let l := Line.Bundles.LineBundle.classOf L
  let m := Line.Bundles.LineBundle.classOf M
  let d := Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
  let px := Line.Bundles.LineBundle.pullbackClassMonoidHom x
  let py := Line.Bundles.LineBundle.pullbackClassMonoidHom y
  let pz := Line.Bundles.LineBundle.pullbackClassMonoidHom z
  have hd : d * px l * py l = pz l := by
    have h : Line.Bundles.LineBundle.classOf
        (((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).tensor ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback x)).tensor
          ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback y)) =
        Line.Bundles.LineBundle.classOf ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback z) :=
      Quotient.sound (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle_formula A L)
    change d * Line.Bundles.LineBundle.pullbackClass x (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) *
      Line.Bundles.LineBundle.pullbackClass y (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) =
        Line.Bundles.LineBundle.pullbackClass z (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) at h
    rw [Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric.identityNormalizedLine_class_overField] at h
    exact h
  have hx : (Product.ShearIsomorphisms.productShearIso A.scheme 1).hom.left ≫ x = z := by
    have h := Product.ShearIsomorphisms.productShearIso_hom_fst A.scheme 1
    rw [zpow_one] at h
    have hm : fst A.scheme A.scheme * snd A.scheme A.scheme = μ[A.scheme] := by
      change lift (fst A.scheme A.scheme) (snd A.scheme A.scheme) ≫ μ[A.scheme] = _
      rw [lift_fst_snd, Category.id_comp]
    exact (congrArg Over.Hom.left h).trans (congrArg Over.Hom.left hm)
  have hy : (Product.ShearIsomorphisms.productShearIso A.scheme 1).hom.left ≫ y = y :=
    congrArg Over.Hom.left (Product.ShearIsomorphisms.productShearIso_hom_snd A.scheme 1)
  have hshear : Line.Bundles.LineBundle.pullbackClass (Product.ShearIsomorphisms.productShearIso A.scheme 1).hom.left
      (Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.externalTensor A.scheme.hom A.scheme.hom
        L (L.reciprocalFrameBundle.tensor M))) = pz l * (py l)⁻¹ * py m := by
    change Line.Bundles.LineBundle.pullbackClass (Product.ShearIsomorphisms.productShearIso A.scheme 1).hom.left
      (Line.Bundles.LineBundle.pullbackClass x l *
        Line.Bundles.LineBundle.pullbackClass y (Line.Bundles.LineBundle.classOf (L.reciprocalFrameBundle.tensor M))) = _
    rw [Line.Bundles.LineBundle.pullbackClass_mul, ← Line.Bundles.LineBundle.pullbackClass_comp,
      ← Line.Bundles.LineBundle.pullbackClass_comp, hx, hy, Line.Bundles.LineBundle.classOf_tensor,
      Line.Bundles.LineBundle.classOf_reciprocalFrameBundle]
    change pz l * py (l⁻¹ * m) = _
    rw [py.map_mul, py.map_inv, mul_assoc]
  rw [hshear]
  change d * px l * py m = pz l * (py l)⁻¹ * py m
  rw [← hd, mul_assoc (d * px l), mul_inv_cancel, mul_one]

theorem differenceTwistedLine_euler
    (H : Line.Bundles.LineBundle A.scheme.left) (hH : H.IsAmple) (L M : Line.Bundles.LineBundle A.scheme.left) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.scheme ⊗ A.scheme).hom (differenceTwistedLine A L M).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom L.sheaf *
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (L.reciprocalFrameBundle.tensor M).sheaf := by
  have : (A.scheme ⊗ A.scheme).left.IsSeparated := by
    constructor
    rw [← terminal.comp_from (A.scheme ⊗ A.scheme).hom]
    have : IsProper (A.scheme ⊗ A.scheme).hom := inferInstanceAs
      (IsProper (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom))
    infer_instance
  calc
    _ = LineBundle.EulerShifts.lineBundleClassEuler (A.scheme ⊗ A.scheme).hom
        (Line.Bundles.LineBundle.classOf (differenceTwistedLine A L M)) := rfl
    _ = LineBundle.EulerShifts.lineBundleClassEuler (A.scheme ⊗ A.scheme).hom
        (Line.Bundles.LineBundle.pullbackClass (Product.ShearIsomorphisms.productShearIso A.scheme 1).hom.left
          (Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.externalTensor A.scheme.hom A.scheme.hom
            L (L.reciprocalFrameBundle.tensor M)))) :=
      congrArg (LineBundle.EulerShifts.lineBundleClassEuler (A.scheme ⊗ A.scheme).hom)
        (differenceTwistedLine_shear_class A L M)
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.scheme ⊗ A.scheme).hom
        (Line.Bundles.LineBundle.externalTensor A.scheme.hom A.scheme.hom L (L.reciprocalFrameBundle.tensor M)).sheaf :=
      LineBundle.ClassEulerIsomorphism.lineBundleClassEuler_pullback_overIso (Product.ShearIsomorphisms.productShearIso A.scheme 1) _
    _ = _ := Ample.SquareExternalEuler.abelianSquare_external_euler A H hH L (L.reciprocalFrameBundle.tensor M)

theorem differenceTwistedLine_exists_nonzero_euler
    (L : Line.Bundles.LineBundle A.scheme.left) (hL : L.IsAmple) (M : Line.Bundles.LineBundle A.scheme.left) :
    ∃ m : ℕ, 0 < m ∧ CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.scheme ⊗ A.scheme).hom
      (differenceTwistedLine A (L.tensorPower m) M).sheaf ≠ 0 := by
  have : Nonempty A.scheme.left := ⟨η[A.scheme].left (IsLocalRing.closedPoint k)⟩
  let E := (hL.exists_powerProjectiveEmbedding A.scheme.hom).some
  obtain ⟨m, hm, hpos, hneg⟩ := E.exists_opposite_nonzero_euler A.scheme.hom
    (Line.Bundles.LineBundle.trivial A.scheme.left) M
  refine ⟨m, hm, ?_⟩
  rw [differenceTwistedLine_euler A L hL]
  apply mul_ne_zero
  · simpa only [Line.Bundles.LineBundle.classOf_trivial, one_mul, zpow_natCast,
      ← Line.Bundles.LineBundle.classOf_tensorPower, LineBundle.EulerShifts.lineBundleClassEuler_classOf] using hpos
  · have he : Line.Bundles.LineBundle.classOf ((L.tensorPower m).reciprocalFrameBundle.tensor M) =
        Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf L ^ (-(m : ℤ)) := by
      rw [Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_reciprocalFrameBundle,
        Line.Bundles.LineBundle.classOf_tensorPower, zpow_neg, zpow_natCast, mul_comm]
    change LineBundle.EulerShifts.lineBundleClassEuler A.scheme.hom
      (Line.Bundles.LineBundle.classOf ((L.tensorPower m).reciprocalFrameBundle.tensor M)) ≠ 0
    rw [he]
    exact hneg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceTwistEuler
