import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitKernelBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs

/-! # Fiber Unit Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.FiberUnitKernel

noncomputable section

/-! The residue fiber of an actual abelian family has only constant
functions. Hence the original unit cycle is a basis for its computed
degree-zero Cech kernel, without any reducedness assumption on the base. -/

universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped _root_.CategoryTheory.MonObj

theorem abelian_field_globalFunctions_isIso
    {k : Type u} [Field k] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) :
    IsIso A.scheme.hom.appTop := by
  let : IsReduced A.scheme.left := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field A.scheme.hom
  exact Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions.isIso_appTop A.scheme.hom η[A.scheme].left η[A.scheme].w

theorem abelianFiber_unitKernelMap_bijective
    {S : Scheme.{u}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (x : S)
    {I : Type u} [LinearOrder I] (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (A.scheme.hom.fiberι x) A.scheme.hom
      (A.scheme.hom.fiberToSpecResidueField x) (S.fromSpecResidueField x)
      (A.scheme.hom.fiber_fac x) (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U φ) 0] :
    Function.Bijective (Cech.UnitKernelBasis.CechModelUnit.baseChangeUnitKernelMap A.scheme.hom
      (S.fromSpecResidueField x) U hU φ) := by
  let : IsIso (A.scheme.hom.fiberToSpecResidueField x).appTop :=
    abelian_field_globalFunctions_isIso (A.pullback (S.fromSpecResidueField x))
  exact Cech.UnitKernelBasis.CechModelUnit.baseChangeUnitKernelMap_bijective (A.scheme.hom.fiberι x) A.scheme.hom
    (A.scheme.hom.fiberToSpecResidueField x) (S.fromSpecResidueField x)
    (A.scheme.hom.fiber_fac x) U hU φ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.FiberUnitKernel
