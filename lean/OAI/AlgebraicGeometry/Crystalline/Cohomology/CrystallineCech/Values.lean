import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.DegreeZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.ZeroDifferential

/-! # Values -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Values.CrystallineCechValues

noncomputable section

/-!
# Values of native zero-cochains on the principal cover

The singleton product is canonically isomorphic to its only factor.
This identifies a zero-cochain component with a section on the original
cover member, and recovers the component by restriction through that
isomorphism. Equality of singleton indices is handled independently of
the chosen categorical product objects.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def singleIso (t : Fin 1 → ι) :
    ((N).obj (op ⦋0⦌)).obj t ≅ CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s (t 0) :=
  productUniqueIso (fun l : Fin 1 => CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s (t l))

def sectionIso (F : Sheaf J V) (t : Fin 1 → ι) :
    F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t))) ≅
      F.obj.obj (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s (t 0)))) :=
  F.obj.mapIso (((CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).mapIso
    (singleIso p k X Q s t)).symm.op)

def component (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0) (t : Fin 1 → ι) :
    F.obj.obj (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t))) :=
  (Pi.π (fun a : ((N).obj (op ⦋0⦌)).I => F.obj.obj
    (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj a)))) t) z

def value (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0) (t : Fin 1 → ι) :
    F.obj.obj (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s (t 0)))) :=
  (sectionIso p k X Q s F t).hom (component p k X Q s F z t)

theorem recover_component (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0) (t : Fin 1 → ι) :
    (sectionIso p k X Q s F t).inv (value p k X Q s F z t) = component p k X Q s F z t :=
  congrArg (fun f => f (component p k X Q s F z t)) (sectionIso p k X Q s F t).hom_inv_id

theorem value_congr (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0)
    {t t' : Fin 1 → ι} (h : t = t') :
    HEq (value p k X Q s F z t) (value p k X Q s F z t') := by
  cases h
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Values.CrystallineCechValues
