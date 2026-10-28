import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.CoefficientEquivalence
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberScalar
import Mathlib.Algebra.Algebra.Equiv

/-! # Residue Unit Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResidueUnitExactness

noncomputable section

/-! Normalize the actual scheme-fiber coefficient map to evaluation in
the residue field. The actual unit map is injective there and its image
is the degree-zero differential kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

def fiberCoefficientEquiv (S : Scheme.{0}) (x : S) :
    letI : Algebra Γ(S, ⊤) Γ(Spec (S.residueField x), ⊤) :=
      (S.fromSpecResidueField x).appTop.hom.toAlgebra
    letI : Algebra Γ(S, ⊤) (S.residueField x) := (S.Γevaluation x).hom.toAlgebra
    Γ(Spec (S.residueField x), ⊤) ≃ₗ[Γ(S, ⊤)] S.residueField x := by
  let : Algebra Γ(S, ⊤) Γ(Spec (S.residueField x), ⊤) :=
    (S.fromSpecResidueField x).appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) (S.residueField x) := (S.Γevaluation x).hom.toAlgebra
  let e := (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv
  let a : Γ(Spec (S.residueField x), ⊤) ≃ₐ[Γ(S, ⊤)] S.residueField x :=
    AlgEquiv.ofRingEquiv (f := e) (fun r =>
      ConcreteCategory.congr_hom (Quotients.FiniteDescent.FiberScalar.Construction.FiberScalarMaps.fromResidue_appTop S x) r)
  exact a.toLinearEquiv

theorem abelianResidue_unit_exactness
    {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (x : S)
    {I : Type} [LinearOrder I] (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{0} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (A.scheme.hom.fiberι x) A.scheme.hom
      (A.scheme.hom.fiberToSpecResidueField x) (S.fromSpecResidueField x)
      (A.scheme.hom.fiber_fac x) (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U φ) 0] :
    letI : Algebra Γ(S, ⊤) (S.residueField x) := (S.Γevaluation x).hom.toAlgebra
    Function.Injective ((Cech.ModelUnit.CechModelUnit.unitMap A.scheme.hom U hU φ).lTensor (S.residueField x)) ∧
      ((D.d 0 1).hom.lTensor (S.residueField x)).ker =
        ((Cech.ModelUnit.CechModelUnit.unitMap A.scheme.hom U hU φ).lTensor (S.residueField x)).range := by
  let : Algebra Γ(S, ⊤) Γ(Spec (S.residueField x), ⊤) :=
    (S.fromSpecResidueField x).appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) (S.residueField x) := (S.Γevaluation x).hom.toAlgebra
  obtain ⟨hu, hex⟩ := Cech.UnitTensorComparison.CechModelUnit.abelianFiber_tensor_unit_conditions A x U hU φ
  exact ⟨Tensor.CoefficientEquivalence.tensorCoefficientEquiv_injective (fiberCoefficientEquiv S x) _ hu,
    Tensor.CoefficientEquivalence.tensorCoefficientEquiv_exact (fiberCoefficientEquiv S x) _ _ hex⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResidueUnitExactness
