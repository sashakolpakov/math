import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDuality

/-! # Free Cech Dual Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDualNaturality.CrystallineFreeCechDualNaturality

noncomputable section

/-!
# Restriction naturality of native free Čech duality

Under the additive coordinate equivalence, precomposition by a native
free Čech map is restriction along the corresponding intersection map.
The proof follows the original sheafification adjunction and free Yoneda
equivalence, preserving the actual section maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "M" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDuality.CrystallineFreeCechDuality.rankOne p k
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

theorem coordinates_natural (F : Sheaf J V) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (a : (presheafToSheaf J V).obj ((FreeCech.CrystallineFreeCech.simplicial p k X Q s M).obj m) ⟶ F)
    (t : ((N).obj n).I) :
    FreeCechDuality.CrystallineFreeCechDuality.coordinates p k X Q s F n
        ((presheafToSheaf J V).map ((FreeCech.CrystallineFreeCech.simplicial p k X Q s M).map f) ≫ a) t =
      F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (((N).map f).φ t)).op
        (FreeCechDuality.CrystallineFreeCechDuality.coordinates p k X Q s F m a (((N).map f).f t)) := by
  let b := FreeCechDuality.CrystallineFreeCechDuality.unadjoint p k X Q s F m a
  let u := Sigma.ι (FreeCechGenerators.CrystallineFreeCechGenerators.family p k X Q s M n) t
  let v := Sigma.ι (FreeCechGenerators.CrystallineFreeCechGenerators.family p k X Q s M m) (((N).map f).f t)
  have ha := (sheafificationAdjunction J V).homEquiv_naturality_left
    ((FreeCech.CrystallineFreeCech.simplicial p k X Q s M).map f) a
  have ho := FreeCechGenerators.CrystallineFreeCechGenerators.outer_naturality p k X Q s M f t
  have hpre : u ≫ FreeCechDuality.CrystallineFreeCechDuality.unadjoint p k X Q s F n
      ((presheafToSheaf J V).map ((FreeCech.CrystallineFreeCech.simplicial p k X Q s M).map f) ≫ a) =
        (FreeCech.CrystallineFreeCech.coefficients p k X Q M).map (((N).map f).φ t) ≫ (v ≫ b) :=
    (congrArg (fun g => u ≫ g) ha).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ b) ho).trans (Category.assoc _ _ _)))
  have hn := SheafInjective.SheafInjectiveRestrictions.presheafHomEquiv_map
    (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (((N).map f).φ t)) M (v ≫ b)
  have hp := congrArg Presheaf.freeYonedaHomEquiv hpre
  exact (FreeCechDuality.CrystallineFreeCechDuality.coordinate_formula p k X Q s F n _ t).trans
    ((congrArg (fun g => g (1 : Site.CoefficientRing p k)) hp).trans
      ((congrArg (fun g => g (1 : Site.CoefficientRing p k)) hn).trans
        (congrArg (F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (((N).map f).φ t)).op)
          (FreeCechDuality.CrystallineFreeCechDuality.coordinate_formula p k X Q s F m a (((N).map f).f t))).symm))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDualNaturality.CrystallineFreeCechDualNaturality
