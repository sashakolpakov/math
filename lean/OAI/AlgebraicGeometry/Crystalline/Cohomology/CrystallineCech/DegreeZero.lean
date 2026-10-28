import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafCechAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Covers

/-! # Degree Zero -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.DegreeZero.CrystallineCechDegreeZero

noncomputable section

/-!
# Separation in degree zero of native principal Čech cochains

The canonical native Čech augmentation is injective for every unit-ideal
principal cover. Its singleton intersections recover each original cover
member, so equality of augmented cochains implies equality of sections
by the native sheaf separation condition.
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

theorem section_ext (F : Sheaf J V) (hs : Ideal.span (Set.range s) = ⊤)
    {x y : F.obj.obj (op Q)}
    (h : ∀ i, F.obj.map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i)).op x =
      F.obj.map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i)).op y) : x = y := by
  apply F.isSeparated Q _ (CrystallinePrincipal.Covers.CrystallinePrincipalCovers.covering_mem p k X Q ι s hs) x y
  intro P f hf
  obtain ⟨T, l, g, hg, rfl⟩ := hf
  obtain ⟨i⟩ := hg
  simpa only [op_comp, F.obj.map_comp, ModuleCat.comp_apply] using
    congrArg (F.obj.map l.op) (h i)

def zeroCoefficientIso (i : ι) :
    ((N).obj (op ⦋0⦌)).obj (fun _ => i) ≅ CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s i :=
  productUniqueIso (fun _ : Fin 1 => CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s i)

theorem component_restriction (F : Sheaf J V) (x : F.obj.obj (op Q)) (i : ι) :
    (Pi.π (fun t : ((N).obj (op ⦋0⦌)).I => F.obj.obj
      (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t)))) (fun _ => i))
        ((SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s F).f 0 x) =
      F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q
        (((N).obj (op ⦋0⦌)).obj (fun _ => i))).op x := by
  exact congrArg (fun f => f x) (Pi.lift_comp_π
    (fun t : ((N).obj (op ⦋0⦌)).I => F.obj.map
      (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (((N).obj (op ⦋0⦌)).obj t)).op) (fun _ => i))

theorem augmentation_injective (F : Sheaf J V) (hs : Ideal.span (Set.range s) = ⊤) :
    Function.Injective ((SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s F).f 0) := by
  intro x y h
  change F.obj.obj (op Q) at x y
  apply section_ext p k X Q s F hs
  intro i
  have hc := congrArg (fun z => (Pi.π (fun t : ((N).obj (op ⦋0⦌)).I => F.obj.obj
    (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t)))) (fun _ => i)) z) h
  have hc' := (component_restriction p k X Q s F x i).symm.trans
    (hc.trans (component_restriction p k X Q s F y i))
  let e := zeroCoefficientIso p k X Q s i
  have hp := (congrArg (fun f => F.obj.map f.op)
    (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k X Q e.inv)).symm.trans (F.obj.map_comp _ _)
  exact (congrArg (fun f => f x) hp).trans
    ((congrArg (F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q e.inv).op) hc').trans
      (congrArg (fun f => f y) hp).symm)

theorem augmentation_mono (F : Sheaf J V) (hs : Ideal.span (Set.range s) = ⊤) :
    Mono ((SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s F).f 0) :=
  (ModuleCat.mono_iff_injective _).mpr (augmentation_injective p k X Q s F hs)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.DegreeZero.CrystallineCechDegreeZero
