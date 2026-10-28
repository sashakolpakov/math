import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCoordinates

/-! # Constant Family Point Fiber -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantFamilyPointFiber.Construction

noncomputable section

/-! A constant family pulled back along a rational point has its original factor as its Cartesian fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

universe u

variable {K : Type u} [Field K] (A S : Over (Spec (.of K)))

def constantFamilyPointFiber (s : 𝟙_ (Over (Spec (.of K))) ⟶ S) : A ⟶ A ⊗ S :=
  lift (𝟙 A) (toUnit A ≫ s)

theorem constantFamilyPointFiber_factor (s : 𝟙_ (Over (Spec (.of K))) ⟶ S) :
    constantFamilyPointFiber A S s ≫ fst A S = 𝟙 A := lift_fst _ _

theorem constantFamilyPointFiber_base (s : 𝟙_ (Over (Spec (.of K))) ⟶ S) :
    constantFamilyPointFiber A S s ≫ snd A S = toUnit A ≫ s := lift_snd _ _

theorem constantFamilyPointFiber_isPullback (s : 𝟙_ (Over (Spec (.of K))) ⟶ S) :
    IsPullback (constantFamilyPointFiber A S s).left A.hom (ConstantProductCoordinates.Construction.constantLeftBase A S) s.left := by
  let p := (fst A S).left
  let f := ConstantProductCoordinates.Construction.constantLeftBase A S
  let j := (constantFamilyPointFiber A S s).left
  have hjp : j ≫ p = 𝟙 A.left := congrArg Over.Hom.left (constantFamilyPointFiber_factor A S s)
  have hjs : j ≫ f = A.hom ≫ s.left := congrArg Over.Hom.left (constantFamilyPointFiber_base A S s)
  have hs : s.left ≫ S.hom = 𝟙 _ := Over.w s
  have ho : IsPullback (j ≫ p) A.hom A.hom (s.left ≫ S.hom) := by
    rw [hjp, hs]
    exact IsPullback.of_id_fst
  exact IsPullback.of_right ho hjs (IsPullback.of_hasPullback A.hom S.hom)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantFamilyPointFiber.Construction
