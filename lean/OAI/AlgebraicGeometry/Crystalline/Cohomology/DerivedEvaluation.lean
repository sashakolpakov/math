import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalHomology
import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Derived Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedEvaluation.CrystallineDerivedEvaluation

noncomputable section

/-!
# Finite-cover effacement of native higher section cohomology

The actual right-derived evaluation functors are defined using native
injective resolutions. Each positive-degree class is killed by restriction
to a finite unit-ideal principal cover. This is local effacement, not a
claim that those classes already vanish on the original object.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

def cohomology (F : Sheaf J V) (Q : Site.Object p k X) (n : ℕ) : V :=
  ((LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q).rightDerived n).obj F

def restriction (F : Sheaf J V) {P Q : Site.Object p k X} (f : P ⟶ Q) (n : ℕ) :
    cohomology p k X F Q n ⟶ cohomology p k X F P n :=
  (NatTrans.rightDerived (LocalHomology.CrystallineLocalHomology.evaluationMap p k X f) n).app F

theorem exists_principal_vanishing (F : Sheaf J V) (Q : Site.Object p k X)
    (n : ℕ) (x : cohomology p k X F Q (n + 1)) :
    ∃ t : Finset Q.thickening.ring, Ideal.span (t : Set Q.thickening.ring) = ⊤ ∧
      ∀ s : t, restriction p k X F
        (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val) (n + 1) x = 0 := by
  let I : InjectiveResolution F := injectiveResolution F
  let e := I.isoRightDerivedObj (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q) (n + 1)
  obtain ⟨t, ht, hv⟩ := LocalHomology.CrystallineLocalHomology.exists_principal_vanishing p k X
    (I.cocomplex.sc (n + 1)) (I.cocomplex_exactAt_succ n) Q (e.hom x)
  refine ⟨t, ht, fun s => ?_⟩
  have he := I.rightDerived_app_eq
    (LocalHomology.CrystallineLocalHomology.evaluationMap p k X
      (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val)) (n + 1)
  dsimp only [restriction]
  rw [he]
  change (I.isoRightDerivedObj (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X
    (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s.val)) (n + 1)).inv
    (ShortComplex.homologyMap (LocalHomology.CrystallineLocalHomology.restriction p k X
      (I.cocomplex.sc (n + 1)) (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val))
        (e.hom x)) = 0
  rw [hv s]
  exact (I.isoRightDerivedObj (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X
    (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s.val)) (n + 1)).inv.hom.map_zero

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedEvaluation.CrystallineDerivedEvaluation
