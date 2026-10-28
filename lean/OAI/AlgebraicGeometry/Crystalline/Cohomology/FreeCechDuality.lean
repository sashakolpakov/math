import OAI.AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.SheafCech

/-! # Free Cech Duality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDuality.CrystallineFreeCechDuality

noncomputable section

/-!
# Degreewise additive duality for native free Čech chains

Morphisms from the rank-one free Čech sheaf term to a native sheaf are
additively equivalent to its actual Čech cochains. Sheafification, the
outer coproduct, free Yoneda, evaluation at one, and the categorical
product isomorphism give the successive canonical equivalences.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k

def rankOne : V := ModuleCat.of R R

def moduleSection (A : SheafInjectives.CrystallineSheafInjectives.Modules p k) : (rankOne p k ⟶ A) ≃+ A :=
  ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ A).toAddEquiv

def presheafSection (P : Site.Object p k X) (F : Sheaf J V) :
    (Presheaf.freeYoneda P (rankOne p k) ⟶ F.obj) ≃+ F.obj.obj (op P) :=
  (Free.YonedaAddEquiv.FreeYonedaAddEquiv.presheaf P (rankOne p k) F.obj).trans (moduleSection p k (F.obj.obj (op P)))

variable (Q : Site.Object p k X) {ι : Type u} (s : ι → Q.thickening.ring)
  (F : Sheaf (Site.topology p k X) (SheafInjectives.CrystallineSheafInjectives.Modules p k))

local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def coordinates (n : SimplexCategoryᵒᵖ) :
    ((presheafToSheaf J V).obj ((FreeCech.CrystallineFreeCech.simplicial p k X Q s (rankOne p k)).obj n) ⟶ F) ≃+
      (∀ t : ((N).obj n).I,
        F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj n).obj t)))) :=
  (((sheafificationAdjunction J V).homAddEquiv
    ((FreeCech.CrystallineFreeCech.simplicial p k X Q s (rankOne p k)).obj n) F).trans
      (Free.YonedaAddEquiv.FreeYonedaAddEquiv.coproduct
        (FreeCechGenerators.CrystallineFreeCechGenerators.family p k X Q s (rankOne p k) n) F.obj)).trans
    (AddEquiv.piCongrRight (fun t => presheafSection p k X
      (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj n).obj t)) F))

def unadjoint (n : SimplexCategoryᵒᵖ)
    (a : (presheafToSheaf J V).obj ((FreeCech.CrystallineFreeCech.simplicial p k X Q s (rankOne p k)).obj n) ⟶ F) :=
  (sheafificationAdjunction J V).homEquiv _ _ a

theorem coordinate_formula (n : SimplexCategoryᵒᵖ)
    (a : (presheafToSheaf J V).obj ((FreeCech.CrystallineFreeCech.simplicial p k X Q s (rankOne p k)).obj n) ⟶ F)
    (t : ((N).obj n).I) :
    coordinates p k X Q s F n a t =
      Presheaf.freeYonedaHomEquiv
        (Sigma.ι (FreeCechGenerators.CrystallineFreeCechGenerators.family p k X Q s (rankOne p k) n) t ≫
          unadjoint p k X Q s F n a) (1 : Site.CoefficientRing p k) := rfl

def homEquiv (n : ℕ) :
    ((FreeCech.CrystallineFreeCech.sheafComplex p k X Q s (rankOne p k)).X n ⟶ F) ≃+
      ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X n :=
  (coordinates p k X Q s F (op ⦋n⦌)).trans
    (ModuleCat.piIsoPi.{u + 1, u, u + 1}
      (fun t : ((N).obj (op ⦋n⦌)).I =>
        F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋n⦌)).obj t))))).symm.toLinearEquiv.toAddEquiv

theorem homEquiv_component (n : ℕ)
    (a : (FreeCech.CrystallineFreeCech.sheafComplex p k X Q s (rankOne p k)).X n ⟶ F)
    (t : ((N).obj (op ⦋n⦌)).I) :
    Pi.π (fun t : ((N).obj (op ⦋n⦌)).I =>
      F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋n⦌)).obj t)))) t
        (CrystallineFreeCechDuality.homEquiv p k X Q s F n a) = coordinates p k X Q s F (op ⦋n⦌) a t := by
  have h := ModuleCat.piIsoPi_inv_kernel_ι.{u + 1, u, u + 1}
    (fun t : ((N).obj (op ⦋n⦌)).I =>
      F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋n⦌)).obj t)))) t
  exact congrArg (fun f => f (coordinates p k X Q s F (op ⦋n⦌) a)) h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDuality.CrystallineFreeCechDuality
