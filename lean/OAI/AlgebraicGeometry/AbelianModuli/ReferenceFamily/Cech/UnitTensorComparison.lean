import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.FiberUnitKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.UnitKernel

/-! # Unit Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitTensorComparison.CechModelUnit

noncomputable section

/-! The actual Cech unit-kernel basis gives exactness of the ordinary
tensor unit map on every residue fiber of the original abelian family. -/

universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

theorem baseChangeUnitKernelMap_eq_tensor
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    {I : Type u} [LinearOrder I] (U : I → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U) [QuasiIsoAt φ 0] :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    UnitKernelBasis.CechModelUnit.baseChangeUnitKernelMap f g U hU φ =
      Tensor.UnitKernel.tensorUnitKernelMap (A := Γ(T, ⊤)) (D.d 0 1).hom (ModelUnit.CechModelUnit.unitMap f U hU φ)
        (ModelUnit.CechModelUnit.differential_unitMap f U hU φ) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  change r • ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤)] (ModelUnit.CechModelUnit.cycle f U hU φ).val) =
    r • ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤)] ModelUnit.CechModelUnit.unitMap f U hU φ 1)
  rw [ModelUnit.CechModelUnit.unitMap_one]

theorem abelianFiber_tensor_unit_conditions
    {S : Scheme.{u}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (x : S)
    {I : Type u} [LinearOrder I] (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (A.scheme.hom.fiberι x) A.scheme.hom
      (A.scheme.hom.fiberToSpecResidueField x) (S.fromSpecResidueField x)
      (A.scheme.hom.fiber_fac x) (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U φ) 0] :
    letI : Algebra Γ(S, ⊤) Γ(Spec (S.residueField x), ⊤) :=
      (S.fromSpecResidueField x).appTop.hom.toAlgebra
    Function.Injective ((ModelUnit.CechModelUnit.unitMap A.scheme.hom U hU φ).lTensor Γ(Spec (S.residueField x), ⊤)) ∧
      ((D.d 0 1).hom.lTensor Γ(Spec (S.residueField x), ⊤)).ker =
        ((ModelUnit.CechModelUnit.unitMap A.scheme.hom U hU φ).lTensor Γ(Spec (S.residueField x), ⊤)).range := by
  let : Algebra Γ(S, ⊤) Γ(Spec (S.residueField x), ⊤) :=
    (S.fromSpecResidueField x).appTop.hom.toAlgebra
  have h := Abelian.FiberUnitKernel.abelianFiber_unitKernelMap_bijective A x U hU φ
  rw [baseChangeUnitKernelMap_eq_tensor A.scheme.hom (S.fromSpecResidueField x) U hU φ] at h
  exact ⟨Tensor.UnitKernel.tensorUnitKernelMap_bijective_injective _ _ _ h,
    Tensor.UnitKernel.tensorUnitKernelMap_bijective_exact _ _ _ h⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitTensorComparison.CechModelUnit
