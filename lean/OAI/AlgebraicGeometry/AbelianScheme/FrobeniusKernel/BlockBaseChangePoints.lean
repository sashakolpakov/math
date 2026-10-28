import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TestBaseChangePoints

/-! # Block Base Change Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockBaseChangePoints.Construction

noncomputable section

/-! The exact CMPoints character-block functor commutes with arbitrary
base change. Both the torsion equation and every integral-action
character equation are transported on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {O : Type} [CommRing O] {S S' : Scheme} {g q : ℕ} [Fact q.Prime]
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
variable (f : S' ⟶ S) (χ : O →+* PadicInt q) (n : ℕ)

theorem l45BlockBaseChangePoints_mem (T : Over S') (x : T ⟶ (A.pullback f).scheme) :
    A.baseChangePointsMulEquiv f T x ∈ PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ n ((Over.map f).obj T) ↔
      x ∈ PELModuli.CMPoints.BlocksProjectors.blockPoints (A.pullback f) (ρ.pullback f) χ n T := by
  let e := A.baseChangePointsMulEquiv f T
  constructor
  · rintro ⟨hp, ha⟩
    constructor
    · apply e.injective
      exact (map_pow e x (q ^ n)).trans (hp.trans e.map_one.symm)
    · intro a
      apply e.injective
      exact (TestBaseChangePoints.Construction.baseChangePoints_postcomp A f A (ρ.map a) T x).trans
        ((ha a).trans (map_pow e x _).symm)
  · rintro ⟨hp, ha⟩
    constructor
    · exact (map_pow e x (q ^ n)).symm.trans ((congrArg e hp).trans e.map_one)
    · intro a
      exact (TestBaseChangePoints.Construction.baseChangePoints_postcomp A f A (ρ.map a) T x).symm.trans
        ((congrArg e (ha a)).trans (map_pow e x _))

def l45BlockBaseChangePointsEquiv (T : Over S') :
    PELModuli.CMPoints.BlocksProjectors.blockPoints (A.pullback f) (ρ.pullback f) χ n T ≃*
      PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ n ((Over.map f).obj T) where
  toFun x := ⟨A.baseChangePointsMulEquiv f T x.val,
    (l45BlockBaseChangePoints_mem A ρ f χ n T x.val).mpr x.property⟩
  invFun y := ⟨(A.baseChangePointsMulEquiv f T).symm y.val, by
    apply (l45BlockBaseChangePoints_mem A ρ f χ n T _).mp
    rw [(A.baseChangePointsMulEquiv f T).apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((A.baseChangePointsMulEquiv f T).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((A.baseChangePointsMulEquiv f T).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext ((A.baseChangePointsMulEquiv f T).map_mul x.val y.val)

def l45BlockFunctorBaseChangeIso :
    PELModuli.CMPoints.BlocksProjectors.blockFunctor (A.pullback f) (ρ.pullback f) χ n ≅
      (Over.map f).op ⋙ PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ χ n :=
  NatIso.ofComponents (fun T => (l45BlockBaseChangePointsEquiv A ρ f χ n T.unop).toGrpIso) (by
    intro T U t
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (TestBaseChangePoints.Construction.baseChangePoints_precomp A f t.unop x.val))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockBaseChangePoints.Construction
