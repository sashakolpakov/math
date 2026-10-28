import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.CoefficientDerivationLift
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Coefficient Derivation Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.CoefficientDerivationSection

noncomputable section

section

/-! Over a field, the proved surjection of coefficient-valued
derivations has a linear section. Affine lifts may therefore be selected
linearly in the original base derivation. -/

variable (k R S C : Type) [Field k] [CommRing R] [CommRing S] [CommRing C]
    [Algebra k R] [Algebra k S] [Algebra k C] [Algebra R S] [Algebra R C] [Algebra S C]
    [IsScalarTower k R S] [IsScalarTower k R C] [IsScalarTower k S C] [IsScalarTower R S C]
    [Algebra.FormallySmooth R S]

theorem exists_smooth_coefficientDerivation_section :
    ∃ L : Derivation k R C →ₗ[k] Derivation k S C,
      ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).restrictScalars k).comp L = LinearMap.id :=
  ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (CoefficientDerivationLift.smooth_coefficientDerivationPrecomposition_surjective k R S C))

def smoothCoefficientDerivationSection : Derivation k R C →ₗ[k] Derivation k S C :=
  (exists_smooth_coefficientDerivation_section k R S C).choose

theorem smoothCoefficientDerivationSection_restrict (d : Derivation k R C) :
    (smoothCoefficientDerivationSection k R S C d).compAlgebraMap R = d :=
  LinearMap.congr_fun (exists_smooth_coefficientDerivation_section k R S C).choose_spec d

theorem smoothCoefficientDerivationSection_algebraMap (d : Derivation k R C) (r : R) :
    smoothCoefficientDerivationSection k R S C d (algebraMap R S r) = d r :=
  Derivation.congr_fun (smoothCoefficientDerivationSection_restrict k R S C d) r

end

/-! Actual affine dual-number lifts with coefficients linear in the
base derivation. The reduction and base restriction are retained as
equalities of the original algebra homomorphisms. -/

variable (k R S C : Type) [Field k] [CommRing R] [CommRing S] [CommRing C]
    [Algebra k R] [Algebra k S] [Algebra k C] [Algebra R S] [Algebra R C] [Algebra S C]
    [IsScalarTower k R S] [IsScalarTower k R C] [IsScalarTower k S C] [IsScalarTower R S C]
    [Algebra.FormallySmooth R S]

def smoothLinearCoefficientLift (d : Derivation k R C) : S →ₐ[k] DualNumber C :=
  ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k S C).symm (smoothCoefficientDerivationSection k R S C d)).val

theorem smoothLinearCoefficientLift_reduction (d : Derivation k R C) :
    (TrivSqZeroExt.fstHom k C C).comp (smoothLinearCoefficientLift k R S C d) =
      IsScalarTower.toAlgHom k S C :=
  ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k S C).symm (smoothCoefficientDerivationSection k R S C d)).property

theorem smoothLinearCoefficientLift_snd (d : Derivation k R C) (s : S) :
    (smoothLinearCoefficientLift k R S C d s).snd = smoothCoefficientDerivationSection k R S C d s :=
  (Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply k S C _ s).symm.trans
    (Derivation.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k S C).apply_symm_apply _) s)

theorem smoothLinearCoefficientLift_base (d : Derivation k R C) :
    (smoothLinearCoefficientLift k R S C d).comp (IsScalarTower.toAlgHom k R S) =
      ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).symm d).val := by
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · have h₁ := AlgHom.congr_fun (smoothLinearCoefficientLift_reduction k R S C d) (algebraMap R S r)
    have h₂ := AlgHom.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).symm d).property r
    exact h₁.trans ((IsScalarTower.algebraMap_apply R S C r).symm.trans h₂.symm)
  · change (smoothLinearCoefficientLift k R S C d (algebraMap R S r)).snd = _
    rw [smoothLinearCoefficientLift_snd, smoothCoefficientDerivationSection_algebraMap]
    exact (Derivation.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).apply_symm_apply d) r).symm.trans
      (Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply k R C _ r)

theorem smoothLinearCoefficientLift_add (d e : Derivation k R C) (s : S) :
    (smoothLinearCoefficientLift k R S C (d + e) s).snd =
      (smoothLinearCoefficientLift k R S C d s).snd + (smoothLinearCoefficientLift k R S C e s).snd := by
  simp only [smoothLinearCoefficientLift_snd, map_add, Derivation.add_apply]

theorem smoothLinearCoefficientLift_smul (a : k) (d : Derivation k R C) (s : S) :
    (smoothLinearCoefficientLift k R S C (a • d) s).snd =
      a • (smoothLinearCoefficientLift k R S C d s).snd := by
  simp only [smoothLinearCoefficientLift_snd, map_smul, Derivation.smul_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.CoefficientDerivationSection
