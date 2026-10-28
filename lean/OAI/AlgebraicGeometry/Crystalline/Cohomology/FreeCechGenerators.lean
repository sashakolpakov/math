import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ArrowSimplicial

/-! # Free Cech Generators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechGenerators.CrystallineFreeCechGenerators

noncomputable section

/-!
# Generators of evaluated native free Čech chains

The generator indexed by an intersection and a native arrow into it
is preserved by the actual simplicial maps. The proof uses the two
coproduct universal properties and postcomposition of native arrows.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q T : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring) (M : SheafInjectives.CrystallineSheafInjectives.Modules p k)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

def family (n : SimplexCategoryᵒᵖ) :=
  fun t : ((N).obj n).I => (FreeCech.CrystallineFreeCech.coefficients p k X Q M).obj (((N).obj n).obj t)

def generator (n : SimplexCategoryᵒᵖ) (z : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s n) :
    M ⟶ ((FreeCech.CrystallineFreeCech.simplicial p k X Q s M).obj n).obj (op T) :=
  Sigma.ι (fun (_ : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj n).obj z.1)) => M) z.2 ≫
    (Sigma.ι (family p k X Q s M n) z.1).app (op T)

theorem outer_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (t : ((N).obj n).I) :
    Sigma.ι (family p k X Q s M n) t ≫ (FreeCech.CrystallineFreeCech.simplicial p k X Q s M).map f =
      (FreeCech.CrystallineFreeCech.coefficients p k X Q M).map (((N).map f).φ t) ≫
        Sigma.ι (family p k X Q s M m) (((N).map f).f t) :=
  Sigma.ι_comp_desc (fun i : ((N).obj n).I =>
    (FreeCech.CrystallineFreeCech.coefficients p k X Q M).map (((N).map f).φ i) ≫
      Sigma.ι (family p k X Q s M m) (((N).map f).f i)) t

theorem inner_naturality {r r' : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring}
    (f : r ⟶ r') (g : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r) :
    Sigma.ι (fun (_ : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r) => M) g ≫
        ((FreeCech.CrystallineFreeCech.coefficients p k X Q M).map f).app (op T) =
      Sigma.ι (fun (_ : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r') => M)
        (g ≫ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q f) :=
  (Sigma.ι_comp_map'
    (f := fun (_ : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r') => M)
    (g := fun (_ : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r) => M)
    (fun g => g ≫ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q f) (fun _ => 𝟙 M) g).trans
      (Category.id_comp _)

theorem naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (z : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s n) :
    generator p k X Q T s M n z ≫ ((FreeCech.CrystallineFreeCech.simplicial p k X Q s M).map f).app (op T) =
      generator p k X Q T s M m (CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.map p k X Q T s f z) := by
  have ho := congrArg (fun a => a.app (op T)) (outer_naturality p k X Q s M f z.1)
  have hi := inner_naturality p k X Q T M (((N).map f).φ z.1) z.2
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => Sigma.ι
      (fun (_ : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj n).obj z.1)) => M) z.2 ≫ a) ho).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫
            (Sigma.ι (family p k X Q s M m) (((N).map f).f z.1)).app (op T)) hi)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechGenerators.CrystallineFreeCechGenerators
