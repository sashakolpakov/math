import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResidueUnitExactness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientPoints

/-! # Coefficient Unit Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness

noncomputable section

/-! The unit of an actual abelian Cech model is injective and generates
the degree-zero kernel after every prescribed field specialization of
the affine base's coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
def coefficientFieldPoint (S : Scheme.{u}) [IsAffine S]
    (k : Type u) [Field k] [Algebra Γ(S, ⊤) k] : Spec (.of k) ⟶ S :=
  CoefficientPoints.affineCoefficientPoint S (algebraMap Γ(S, ⊤) k)

def coefficientFieldSectionsEquiv (S : Scheme.{u}) [IsAffine S]
    (k : Type u) [Field k] [Algebra Γ(S, ⊤) k] :
    letI : Algebra Γ(S, ⊤) Γ(Spec (.of k), ⊤) := (coefficientFieldPoint S k).appTop.hom.toAlgebra
    Γ(Spec (.of k), ⊤) ≃ₗ[Γ(S, ⊤)] k := by
  let : Algebra Γ(S, ⊤) Γ(Spec (.of k), ⊤) := (coefficientFieldPoint S k).appTop.hom.toAlgebra
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  let a : Γ(Spec (.of k), ⊤) ≃ₐ[Γ(S, ⊤)] k :=
    AlgEquiv.ofRingEquiv (f := e) (fun r =>
      RingHom.congr_fun (CoefficientPoints.affineCoefficientPoint_coefficients S (algebraMap Γ(S, ⊤) k)) r)
  exact a.toLinearEquiv

theorem abelianCoefficient_unit_exactness
    {S : Scheme.{u}} [IsAffine S] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (k : Type u) [Field k] [Algebra Γ(S, ⊤) k]
    {I : Type u} [LinearOrder I] (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap
      (pullback.fst A.scheme.hom (coefficientFieldPoint S k)) A.scheme.hom
      (pullback.snd A.scheme.hom (coefficientFieldPoint S k)) (coefficientFieldPoint S k)
      pullback.condition (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U φ) 0] :
    Function.Injective ((Cech.ModelUnit.CechModelUnit.unitMap A.scheme.hom U hU φ).lTensor k) ∧
      ((D.d 0 1).hom.lTensor k).ker = ((Cech.ModelUnit.CechModelUnit.unitMap A.scheme.hom U hU φ).lTensor k).range := by
  let q := coefficientFieldPoint S k
  let : Algebra Γ(S, ⊤) Γ(Spec (.of k), ⊤) := q.appTop.hom.toAlgebra
  let : IsIso (pullback.snd A.scheme.hom q).appTop :=
    Abelian.FiberUnitKernel.abelian_field_globalFunctions_isIso (A.pullback q)
  have h := Cech.UnitKernelBasis.CechModelUnit.baseChangeUnitKernelMap_bijective
    (pullback.fst A.scheme.hom q) A.scheme.hom (pullback.snd A.scheme.hom q) q
    pullback.condition U hU φ
  rw [Cech.UnitTensorComparison.CechModelUnit.baseChangeUnitKernelMap_eq_tensor A.scheme.hom q U hU φ] at h
  have hu := Tensor.UnitKernel.tensorUnitKernelMap_bijective_injective _ _ _ h
  have hex := Tensor.UnitKernel.tensorUnitKernelMap_bijective_exact _ _ _ h
  exact ⟨Tensor.CoefficientEquivalence.tensorCoefficientEquiv_injective (coefficientFieldSectionsEquiv S k) _ hu,
    Tensor.CoefficientEquivalence.tensorCoefficientEquiv_exact (coefficientFieldSectionsEquiv S k) _ _ hex⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness
