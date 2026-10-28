import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular

/-! # Absolute Product Maps -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AbsoluteProductMaps.Constructions

noncomputable section

/-! Ordinary exterior cup pullback along an actual map into a product,
with its genuine projections and explicit cohomological degree transport. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions OAI.AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem absoluteDegreeCast_apply (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X m) :
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X) h) a =
      cast (congrArg (fun k => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X k : Type)) h) a := by
  subst n
  rfl

theorem absolutePullback_degreeCast {X Y : TopCat.{0}} (f : X ⟶ Y) {m n : ℕ} (h : m = n)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y m) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n
      (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y) h) a) =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X) h)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f m a) := by
  subst n
  rfl

theorem evenAbsoluteExteriorCup_pullback {X Y Z : TopCat.{0}} (f : Z ⟶ TopCat.of (X × Y))
    (p q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f (2 * (p + q)) (ExteriorCupForget.Constructions.evenAbsoluteExteriorCup X Y p q a b) =
      eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Z) (Nat.mul_add 2 p q).symm)
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) Z (2 * p) (2 * q)
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (f ≫ TopCat.prodFst) (2 * p) a)
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (f ≫ TopCat.prodSnd) (2 * q) b)) := by
  unfold ExteriorCupForget.Constructions.evenAbsoluteExteriorCup
  rw [absolutePullback_degreeCast f (Nat.mul_add 2 p q).symm, AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback]
  simp only [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp, ConcreteCategory.comp_apply]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AbsoluteProductMaps.Constructions
