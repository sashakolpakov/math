import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResiduePrime
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExtensionSectionDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberEulerGroundField
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Module Residue Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ModuleResidueRank

noncomputable section

/-! A bijective residue section comparison identifies the stalk rank of a
finite projective global-section module with the actual fiber section dimension. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

theorem sectionModule_rankAtStalk_of_residueComparison
    {S X : Scheme.{u}} (f : X ⟶ S) (L : Line.Bundles.LineBundle X)
    [Module.Finite Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf)]
    [Module.Projective Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf)]
    (x : S)
    (h : Function.Bijective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison
      (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L.sheaf).app (.op ⊤))) :
    Module.rankAtStalk ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf) (S.toSpecΓ x) =
      FiberEulerGroundField.lineBundleFieldSectionDimension (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)) := by
  let b := S.fromSpecResidueField x
  let M := (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf
  let K := Γ(Spec (S.residueField x), ⊤)
  let : Field K := ((Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField (S.residueField x))).toField
  let : Algebra Γ(S, ⊤) K := b.appTop.hom.toAlgebra
  let T := TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra b) M
  let tensorModule : Module Γ(Spec (S.residueField x), ⊤)
      (TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra b)
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (.op ⊤))) := by
    change Module (Affine.TensorSectionComparison.morphismGlobalAlgebra b)
      (TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra b)
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (.op ⊤)))
    infer_instance
  let : Module K T := tensorModule
  let p : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  let e := LinearEquiv.ofBijective
    (Scalar.SectionBaseChange.baseChangeGlobalSectionsLinearMap (IsPullback.of_hasPullback f b) L.sheaf) h
  calc
    Module.rankAtStalk M (S.toSpecΓ x) = Module.rankAtStalk M (p.comap b.appTop.hom) :=
      congrArg (Module.rankAtStalk M) (Affine.ResiduePrime.residuePoint_prime_comap S x p).symm
    _ = Module.rankAtStalk (R := K) T p :=
      (Module.rankAtStalk_baseChange (R := Γ(S, ⊤)) (M := M) (S := Affine.TensorSectionComparison.morphismGlobalAlgebra b) p).symm
    _ = Module.finrank K T := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := T)) p
    _ = Module.finrank K ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor (f.fiberToSpecResidueField x).appTop.hom).obj
        (L.pullback (f.fiberι x)).sheaf) := e.finrank_eq
    _ = FiberEulerGroundField.lineBundleFieldSectionDimension (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)) :=
      (HilbertConstruction.Field.ExtensionSectionDimension.schemeGlobalSections_finrank_eq_globalCoefficients (f.fiberToSpecResidueField x)
        (L.pullback (f.fiberι x)).sheaf).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ModuleResidueRank
