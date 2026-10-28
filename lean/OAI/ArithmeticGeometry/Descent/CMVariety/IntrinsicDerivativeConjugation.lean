import OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialNaturality
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Intrinsic Derivative Conjugation -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian

noncomputable section

section

/-!
The actual complex differential of a group-preserving scheme isomorphism
identifies the native exponential lattices. Both the differential and
its compatibility with the exponential are proved from the scheme map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [GrpObj X] [GrpObj Y]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

def nativeSchemeIsoHomeomorph (e : X ≅ Y) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y where
  toFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
  invFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.inv
  left_inv x := by
    change (x ≫ e.hom) ≫ e.inv = x
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv x := by
    change (x ≫ e.inv) ≫ e.hom = x
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  continuous_toFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _
  continuous_invFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _

omit [GrpObj X] [GrpObj Y] in
theorem nativeSchemeIso_mdifferentiable (e : X ≅ Y) :
    (nativeSchemeIsoHomeomorph e).toOpenPartialHomeomorph.MDifferentiable
      (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) := by
  constructor
  · exact ((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map e.hom 1).mdifferentiable (by simp)).mdifferentiableOn
  · exact ((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map e.inv 1).mdifferentiable (by simp)).mdifferentiableOn

def nativeSchemeIsoTangent (e : X ≅ Y) : ModelX ≃L[ℂ] ModelY :=
  (nativeSchemeIso_mdifferentiable e).mfderiv (x := (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Set.mem_univ _)

omit [GrpObj Y] in
theorem nativeSchemeIsoTangent_real (e : X ≅ Y) :
    (show ModelX →L[ℝ] ModelY from
      mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom) 1) =
        (nativeSchemeIsoTangent e).toContinuousLinearMap.restrictScalars ℝ :=
  AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_nativeScheme_map_eq_restrictScalars e.hom 1

variable [IsCommMonObj X] [IsCommMonObj Y]
  [T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]

local instance : LieGroup (𝓘(ℝ, ModelX)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup X
local instance : LieGroup (𝓘(ℝ, ModelY)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup Y

theorem nativeSchemeIsoTangent_exp (e : X ≅ Y) [IsMonHom e.hom] (v : ModelX) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) v) =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (nativeSchemeIsoTangent e v) := by
  let f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X →* AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y :=
    { toFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
      map_one' := MonObj.one_comp e.hom
      map_mul' := fun x y => MonObj.mul_comp x y e.hom }
  have hf : MDifferentiable (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) f :=
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map e.hom 1).mdifferentiable (by simp)
  have h := ExponentialNaturality.Abelian.groupMap_exp f hf (show GroupLieAlgebra (𝓘(ℝ, ModelX)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) from v)
  have hd := congrArg (fun D : ModelX →L[ℝ] ModelY => D v) (nativeSchemeIsoTangent_real e)
  exact h.trans (congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) hd)

/-- Membership in the genuine exponential kernel is preserved and reflected. -/
theorem nativeSchemeIsoTangent_mem_lattice_iff (e : X ≅ Y) [IsMonHom e.hom] (v : ModelX) :
    nativeSchemeIsoTangent e v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expLattice (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ↔
      v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expLattice (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (nativeSchemeIsoTangent e v) = 1 ↔
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) v = 1
  rw [← nativeSchemeIsoTangent_exp e]
  have h1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom 1 = 1 := MonObj.one_comp e.hom
  rw [← h1]
  exact (nativeSchemeIsoHomeomorph e).injective.eq_iff

end

/-!
The derivative of a transported actual endomorphism is conjugate by the
actual tangent map of the geometric scheme presentation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

section DifferentialSquare

variable {E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [One G]
  [TopologicalSpace H] [ChartedSpace F H] [One H]

theorem identity_derivative_commuting_square
    (f : G → H) (k : G → G) (l : H → H)
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) f 1)
    (hk : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) k 1)
    (hl : MDifferentiableAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) l 1)
    (hf1 : f 1 = 1) (hk1 : k 1 = 1) (h : f ∘ k = l ∘ f) (v : E) :
    mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) l 1
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f 1 v) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f 1
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) k 1 v) := by
  have hleft := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, F)) (1 : G) (hk1 ▸ hf) hk
  have hright := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    (I'' := 𝓘(ℝ, F)) (1 : G) (hf1 ▸ hl) hf
  rw [h, hright, hf1, hk1] at hleft
  exact congrArg (fun D : E →L[ℝ] F => D v) hleft

end DifferentialSquare

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [GrpObj X] [GrpObj Y]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

theorem nativeSchemeIsoTangent_conjugate
    (e : X ≅ Y) [IsMonHom e.hom] (k : X ⟶ X) [IsMonHom k] (v : ModelX) :
    mfderiv (𝓘(ℝ, ModelY)) (𝓘(ℝ, ModelY))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (e.inv ≫ k ≫ e.hom)) 1 (nativeSchemeIsoTangent e v) =
      nativeSchemeIsoTangent e
        (mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelX)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k) 1 v) := by
  let f := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
  let K := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k
  let L := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (e.inv ≫ k ≫ e.hom)
  have hsq : f ∘ K = L ∘ f := by
    funext x
    change (x ≫ k) ≫ e.hom = (x ≫ e.hom) ≫ (e.inv ≫ k ≫ e.hom)
    simp only [Category.assoc, e.hom_inv_id_assoc]
  have h := identity_derivative_commuting_square f K L
    (((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map e.hom 1).mdifferentiable (by simp)) 1)
    (((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map k 1).mdifferentiable (by simp)) 1)
    (((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (e.inv ≫ k ≫ e.hom) 1).mdifferentiable (by simp)) 1)
    (MonObj.one_comp e.hom) (MonObj.one_comp k) hsq v
  have he (w : ModelX) :
      mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) f 1 w = nativeSchemeIsoTangent e w :=
    congrArg (fun D : ModelX →L[ℝ] ModelY => D w) (nativeSchemeIsoTangent_real e)
  exact (congrArg (fun w : ModelY => mfderiv (𝓘(ℝ, ModelY)) (𝓘(ℝ, ModelY)) L 1 w)
    (he v).symm).trans (h.trans (he _))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian
