import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients

/-! # Coefficient Lift Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality

noncomputable section

section

/-! Pulling back the functions of an actual affine dual-number lift
is linear over its coefficient ring. The constructed linear map retains
the original algebra-map composition. -/

variable (k B D C : Type) [CommRing k] [CommRing B] [CommRing D] [CommRing C]
    [Algebra k B] [Algebra k D] [Algebra k C] [Algebra B D] [Algebra B C] [Algebra D C]
    [IsScalarTower k B D] [IsScalarTower k B C] [IsScalarTower k D C] [IsScalarTower B D C]

def coefficientDerivationPrecomposition : Derivation k D C →ₗ[C] Derivation k B C where
  toFun d := d.compAlgebraMap B
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualCoefficientLiftPrecomposition : AlgebraLiftCoordinates.DualCoefficientLifts.Space C k D →ₗ[C] AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B :=
  (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).symm.toLinearMap.comp
    ((coefficientDerivationPrecomposition k B D C).comp (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k D).toLinearMap)

omit [CommRing D] [Algebra k D] [Algebra B D] [Algebra D C]
    [IsScalarTower k B D] [IsScalarTower k D C] [IsScalarTower B D C] in
theorem dualCoefficientLift_fst (v : AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B) (b : B) :
    (v.val.hom b).fst = algebraMap B C b := by
  have h := v.val.congruent b
  change (v.val.hom b - algebraMap B (DualNumber C) b).fst = 0 at h
  rw [TrivSqZeroExt.fst_sub, IsScalarTower.algebraMap_apply B C (DualNumber C),
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl] at h
  exact sub_eq_zero.mp h

theorem dualCoefficientLiftPrecomposition_hom (v : AlgebraLiftCoordinates.DualCoefficientLifts.Space C k D) (b : B) :
    (dualCoefficientLiftPrecomposition k B D C v).val.hom b = v.val.hom (algebraMap B D b) := by
  apply TrivSqZeroExt.ext
  · rw [dualCoefficientLift_fst, dualCoefficientLift_fst]
    exact IsScalarTower.algebraMap_apply B D C b
  · have h : AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B (dualCoefficientLiftPrecomposition k B D C v) =
        coefficientDerivationPrecomposition k B D C (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k D v) :=
      (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).apply_symm_apply _
    have hb := Derivation.congr_fun h b
    rw [AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv_apply] at hb
    exact hb.trans (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv_apply C k D v (algebraMap B D b))

end

/-! Changing coefficient algebras acts linearly on actual dual-number
lifts and retains their literal ring maps. Smooth conormal coordinates
commute with the same change of coefficients. -/

variable (k B C C' : Type) [CommRing k] [CommRing B] [CommRing C] [CommRing C']
    [Algebra k B] [Algebra k C] [Algebra k C'] [Algebra B C] [Algebra B C']
    [IsScalarTower k B C] [IsScalarTower k B C'] (q : C →ₐ[B] C')

instance dualCoefficientLift_baseModule : Module k (AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B) :=
  Module.compHom (AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B) (algebraMap k C)

instance dualCoefficientLift_baseScalarTower : IsScalarTower k C (AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def coefficientDerivationMap : Derivation k B C →ₗ[k] Derivation k B C' :=
  (q.toLinearMap.compDer).restrictScalars k

def dualCoefficientLiftMap : AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B →ₗ[k] AlgebraLiftCoordinates.DualCoefficientLifts.Space C' k B :=
  ((AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C' k B).symm.restrictScalars k).toLinearMap.comp
    ((coefficientDerivationMap k B C C' q).comp
      ((AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).restrictScalars k).toLinearMap)

theorem dualCoefficientLiftMap_hom (v : AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B) (b : B) :
    (dualCoefficientLiftMap k B C C' q v).val.hom b = NumberCoefficients.dualNumberRingMap q.toRingHom (v.val.hom b) := by
  apply TrivSqZeroExt.ext
  · change ((dualCoefficientLiftMap k B C C' q v).val.hom b).fst = q (v.val.hom b).fst
    rw [dualCoefficientLift_fst, dualCoefficientLift_fst]
    exact (q.commutes b).symm
  · have h : AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C' k B (dualCoefficientLiftMap k B C C' q v) =
        coefficientDerivationMap k B C C' q (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B v) :=
      (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C' k B).apply_symm_apply _
    have hb := Derivation.congr_fun h b
    rw [AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv_apply] at hb
    change ((dualCoefficientLiftMap k B C C' q v).val.hom b).snd =
      q (AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B v b) at hb
    rw [AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv_apply] at hb
    exact hb

variable [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C] [IsScalarTower B k C']
    [Algebra.FormallySmooth k B]

theorem dualCoefficientLiftMap_conormal (v : AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B)
    (z : (RingHom.ker (algebraMap B k)).Cotangent) :
    AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv C' k B (dualCoefficientLiftMap k B C C' q v) z =
      q (AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv C k B v z) := by
  obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap B k)) z
  rw [AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv_toCotangent, AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv_toCotangent,
    dualCoefficientLiftMap_hom]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality
