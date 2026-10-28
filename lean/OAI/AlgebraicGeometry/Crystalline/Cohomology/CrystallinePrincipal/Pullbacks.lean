import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Pullbacks -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Pullbacks.CrystallinePrincipalPullbacks

noncomputable section

/-!
# Actual pullbacks of crystalline principal opens

Pulling back the principal open defined by s along a native crystalline
map gives the principal open defined by the image of s. The constructed
square satisfies the categorical pullback universal property inside the
original crystalline category.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  {P Q : Site.Object p k X} (f : P ⟶ Q) (s : Q.thickening.ring)

theorem baseChange_unit : IsUnit
    ((Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s) ≫ f).ambientMap s) := by
  change IsUnit (algebraMap P.thickening.ring (Localization.Away (f.ambientMap s)) (f.ambientMap s))
  exact IsLocalization.Away.algebraMap_isUnit (f.ambientMap s)

def map : Opens.CrystallinePrincipalOpens.object p k X P (f.ambientMap s) ⟶
    Opens.CrystallinePrincipalOpens.object p k X Q s :=
  Factorization.CrystallinePrincipalFactorization.lift p k X
    (Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s) ≫ f) s (baseChange_unit p k X f s)

theorem condition : CrystallinePrincipalPullbacks.map p k X f s ≫ Opens.CrystallinePrincipalOpens.projection p k X Q s =
    Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s) ≫ f :=
  Factorization.CrystallinePrincipalFactorization.lift_projection p k X
    (Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s) ≫ f) s (baseChange_unit p k X f s)

/-- The ordinary base-change rule for principal opens holds in the actual crystalline category. -/
theorem isPullback : IsPullback (CrystallinePrincipalPullbacks.map p k X f s)
    (Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s))
    (Opens.CrystallinePrincipalOpens.projection p k X Q s) f := by
  apply IsPullback.mk' (condition p k X f s)
  · intro Z g h _ h₂
    exact (cancel_mono (Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s))).mp h₂
  · intro Z a b hab
    have hu : IsUnit ((Opens.CrystallinePrincipalOpens.projection p k X Q s).ambientMap s) := by
      change IsUnit (algebraMap Q.thickening.ring (Localization.Away s) s)
      exact IsLocalization.Away.algebraMap_isUnit s
    have hb : IsUnit (b.ambientMap (f.ambientMap s)) := by
      have ha := hu.map a.ambientMap
      have he := congrArg (fun g : Z ⟶ Q => g.ambientMap s) hab
      exact he ▸ ha
    let l := Factorization.CrystallinePrincipalFactorization.lift p k X b (f.ambientMap s) hb
    have hl : l ≫ Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s) = b :=
      Factorization.CrystallinePrincipalFactorization.lift_projection p k X b (f.ambientMap s) hb
    refine ⟨l, ?_, hl⟩
    apply (cancel_mono (Opens.CrystallinePrincipalOpens.projection p k X Q s)).mp
    rw [Category.assoc, condition, ← Category.assoc, hl]
    exact hab.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Pullbacks.CrystallinePrincipalPullbacks
