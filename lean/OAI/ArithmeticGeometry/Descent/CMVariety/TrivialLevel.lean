import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Trivial Level -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.TrivialLevel.Abelian

noncomputable section

/-! The order-one full level exists for every abelian scheme. This allows
the fixed-enhancement rigidity theorem to be used for unmarked families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem torsionOne_subsingleton {g : ℕ} {S : Scheme} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    Subsingleton (A.torsionPoints 1 T) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx : x.val = 1 := by
    simpa only [pow_one] using (A.mem_torsionPoints 1 T x.val).mp x.property
  have hy : y.val = 1 := by
    simpa only [pow_one] using (A.mem_torsionPoints 1 T y.val).mp y.property
  exact hx.trans hy.symm

def trivialFullLevel {g : ℕ} {S : Scheme} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) : A.FullLevel 1 := by
  have (T : Over S) : Subsingleton (A.torsionPoints 1 T) := torsionOne_subsingleton A T
  let e (T : Over S) :
      LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod 1)) ≃* A.torsionPoints 1 T := {
    toFun := fun _ => 1
    invFun := fun _ => 1
    left_inv := fun _ => by
      apply LocallyConstant.ext
      intro x
      apply Multiplicative.toAdd.injective
      funext j
      exact Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    map_mul' := fun _ _ => by simp }
  exact NatIso.ofComponents (fun T => MulEquiv.toGrpIso (e T.unop)) (by
    intro T U f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact @Subsingleton.elim (A.torsionPoints 1 U.unop) (torsionOne_subsingleton A U.unop) _ _)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.TrivialLevel.Abelian
