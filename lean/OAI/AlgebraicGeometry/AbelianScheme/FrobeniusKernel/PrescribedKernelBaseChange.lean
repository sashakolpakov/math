import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TestBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardMapBaseChange

/-! # Prescribed Kernel Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedKernelBaseChange.Construction

noncomputable section

/-! The all-test-scheme prescribed kernel property commutes with
arbitrary base change. The proof uses the actual pullback adjunction,
and does not discard nilpotent test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S S' : Scheme.{u}} {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S} {H : Over S}
variable (f : S' ⟶ S) (p : A.scheme ⟶ B.scheme) (i : H ⟶ A.scheme)

theorem prescribedKernel_baseChange (hp : Prescribed.Construction.PrescribedKernel p i) :
    Prescribed.Construction.PrescribedKernel (PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p) ((Over.pullback f).map i) := by
  let : GrpObj ((Over.pullback f).obj A.scheme) := Functor.grpObjObj
  let : GrpObj ((Over.pullback f).obj B.scheme) := Functor.grpObjObj
  intro T a
  let eA := A.baseChangePointsMulEquiv f T
  let eB := B.baseChangePointsMulEquiv f T
  let eH := ((Over.mapPullbackAdj f).homEquiv T H).symm
  have hpost : eB (a ≫ (Over.pullback f).map p) = eA a ≫ p :=
    TestBaseChangePoints.Construction.baseChangePoints_postcomp A f B p T a
  have hker : a ≫ (Over.pullback f).map p = 1 ↔ eA a ≫ p = 1 := by
    constructor
    · intro ha
      exact hpost.symm.trans ((congrArg eB ha).trans eB.map_one)
    · intro ha
      apply eB.injective
      exact hpost.trans (ha.trans eB.map_one.symm)
  have hlift : (∃! z : T ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map i = a) ↔
      ∃! z : (Over.map f).obj T ⟶ H, z ≫ i = eA a := by
    apply eH.existsUnique_congr
    intro z
    have hnat : eA (z ≫ (Over.pullback f).map i) = eH z ≫ i := by
      apply Over.OverMorphism.ext
      change (z.left ≫ ((Over.pullback f).map i).left) ≫
          CategoryTheory.Limits.pullback.fst A.scheme.hom f =
        (z.left ≫ CategoryTheory.Limits.pullback.fst H.hom f) ≫ i.left
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun r => z.left ≫ r) (CategoryTheory.Limits.pullback.lift_fst _ _ _)).trans
          (Category.assoc _ _ _).symm)
    constructor
    · intro hz
      exact hnat.symm.trans (congrArg eA hz)
    · intro hz
      apply eA.injective
      exact hnat.trans hz
  exact hker.trans ((hp ((Over.map f).obj T) (eA a)).trans hlift.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedKernelBaseChange.Construction
