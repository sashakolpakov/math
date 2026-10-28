import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.StructureCechModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.UnitKernelContraction

/-! # Cech Unit Contraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian

noncomputable section

/-! The constructed abelian structure-sheaf Cech model admits a global
degree-zero contraction over its original affine coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{0}} [IsAffine S] {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (F : StructureCechModel.AbelianStructureCechModel A)

theorem StructureCechModel.AbelianStructureCechModel.field_unit_exactness (k : Type) [Field k] [Algebra Γ(S, ⊤) k] :
    Function.Injective (F.unitMap.lTensor k) ∧
      ((F.complex.d 0 1).hom.lTensor k).ker = (F.unitMap.lTensor k).range := by
  let := F.quasi
  let q := Affine.CoefficientUnitExactness.coefficientFieldPoint S k
  let : QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (pullback.fst A.scheme.hom q) A.scheme.hom
      (pullback.snd A.scheme.hom q) q pullback.condition (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) F.opens F.comparison) :=
    F.baseChange _ _ (pullback.fst A.scheme.hom q) (pullback.snd A.scheme.hom q) q
      (IsPullback.of_hasPullback A.scheme.hom q)
  exact Affine.CoefficientUnitExactness.abelianCoefficient_unit_exactness A k F.opens F.covers F.comparison

theorem StructureCechModel.AbelianStructureCechModel.unit_contraction :
    ∃ (s : F.complex.X 0 →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
      (v : F.complex.X 1 →ₗ[Γ(S, ⊤)] F.complex.X 0),
      s.comp F.unitMap = LinearMap.id ∧
        v.comp (F.complex.d 0 1).hom + F.unitMap.comp s = LinearMap.id := by
  let : Module.Finite Γ(S, ⊤) (F.complex.X 0) := F.finite 0
  let : Module.Finite Γ(S, ⊤) (F.complex.X 1) := F.finite 1
  let : Module.Projective Γ(S, ⊤) (F.complex.X 0) := F.projective 0
  let : Module.Projective Γ(S, ⊤) (F.complex.X 1) := F.projective 1
  apply Global.UnitKernelContraction.global_kernel_contraction_of_residue_unit (F.complex.d 0 1).hom F.unitMap F.differential_unitMap
  · intro P hP
    exact (F.field_unit_exactness (IsLocalRing.ResidueField (Localization.AtPrime P))).1
  · intro P hP
    exact (F.field_unit_exactness (IsLocalRing.ResidueField (Localization.AtPrime P))).2

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian
