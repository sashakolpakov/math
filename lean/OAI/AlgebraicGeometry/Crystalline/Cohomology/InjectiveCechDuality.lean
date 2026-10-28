import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDualNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SimplicialInjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafCechAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Injective Cech Duality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCechDuality.CrystallineInjectiveCechDuality

noncomputable section

/-!
# The native Čech complex as the additive dual of free Čech chains

The degreewise section equivalences commute with every coface and
codegeneracy. They therefore identify the actual native Čech cochains,
after forgetting scalars, with morphisms from the free Čech sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial _root_.AlgebraicTopology

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "M" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDuality.CrystallineFreeCechDuality.rankOne p k
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def sheafSimplicial : SimplicialObject (Sheaf J V) :=
  FreeCech.CrystallineFreeCech.simplicial p k X Q s M ⋙ presheafToSheaf J V

def homCosimplicial (F : Sheaf J V) : CosimplicialObject AddCommGrpCat.{u + 1} :=
  SimplicialInjective.SimplicialInjectiveHom.cosimplicial (sheafSimplicial p k X Q s) F

def sectionCosimplicial (F : Sheaf J V) : CosimplicialObject V :=
  (SheafCechAugmentation.CrystallineSheafCechAugmentation.cosimplicialFunctor p k X Q s).obj F

theorem section_component (F : Sheaf J V) {n m : SimplexCategory} (f : n ⟶ m)
    (z : (sectionCosimplicial p k X Q s F).obj n) (t : ((N).obj (op m)).I) :
    Pi.π (fun a : ((N).obj (op m)).I =>
      F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op m)).obj a)))) t
        ((sectionCosimplicial p k X Q s F).map f z) =
      F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (((N).map f.op).φ t)).op
        (Pi.π (fun a : ((N).obj (op n)).I =>
          F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op n)).obj a))))
            (((N).map f.op).f t) z) :=
  congrArg (fun g => g z) (Pi.lift_comp_π
    (fun a : ((N).obj (op m)).I =>
      Pi.π (fun b : ((N).obj (op n)).I =>
        F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op n)).obj b))))
          (((N).map f.op).f a) ≫
      F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (((N).map f.op).φ a)).op) t)

def cosimplicialIso (F : Sheaf J V) : homCosimplicial p k X Q s F ≅
    sectionCosimplicial p k X Q s F ⋙ forget₂ V AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun n => (FreeCechDuality.CrystallineFreeCechDuality.homEquiv p k X Q s F n.len).toAddCommGrpIso)
    (by
      intro n m f
      apply AddCommGrpCat.ext
      intro a
      apply Concrete.limit_ext (Discrete.functor (fun t : ((N).obj (op m)).I =>
        F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op m)).obj t)))))
      intro t
      have hl := FreeCechDuality.CrystallineFreeCechDuality.homEquiv_component p k X Q s F m.len
        ((presheafToSheaf J V).map ((FreeCech.CrystallineFreeCech.simplicial p k X Q s M).map f.op) ≫ a) t.as
      have hn := FreeCechDualNaturality.CrystallineFreeCechDualNaturality.coordinates_natural p k X Q s F f.op a t.as
      have hr := FreeCechDuality.CrystallineFreeCechDuality.homEquiv_component p k X Q s F n.len a
        (((N).map f.op).f t.as)
      have hc := section_component p k X Q s F f
        (FreeCechDuality.CrystallineFreeCechDuality.homEquiv p k X Q s F n.len a) t.as
      exact hl.trans (hn.trans
        ((congrArg (F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (((N).map f.op).φ t.as)).op) hr).symm.trans hc.symm)))

def complexIso (F : Sheaf J V) :
    SimplicialInjective.SimplicialInjectiveHom.complex (sheafSimplicial p k X Q s) F ≅
      ((forget₂ V AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F) :=
  (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso (cosimplicialIso p k X Q s F) ≪≫
    (Cech.CoefficientChange.CechCoefficientChange.mapCofaceIso (forget₂ V AddCommGrpCat.{u + 1})
      (sectionCosimplicial p k X Q s F)).symm

def sheafChainIso : FreeCech.CrystallineFreeCech.sheafComplex p k X Q s M ≅
    AlternatingFaceMapComplex.obj (sheafSimplicial p k X Q s) :=
  eqToIso (congrArg (fun F => F.obj (FreeCech.CrystallineFreeCech.simplicial p k X Q s M))
    (map_alternatingFaceMapComplex (presheafToSheaf J V)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCechDuality.CrystallineInjectiveCechDuality
