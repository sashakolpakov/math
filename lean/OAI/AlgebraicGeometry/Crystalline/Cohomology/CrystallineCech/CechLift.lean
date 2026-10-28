import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Gluing

/-! # Cech Lift -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.CechLift.CrystallineCechLift

noncomputable section

/-!
# Lifting augmented sections to native zero-cochains

Local preimages on the original principal cover determine a cochain by
restriction to its singleton intersections. Naturality identifies the
image of this cochain with the actual augmentation of the given section.
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

def assemble (F : Sheaf J V)
    (y : ∀ i, F.obj.obj (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s i)))) :
    ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0 :=
  (ModuleCat.piIsoPi.{u + 1, u, u + 1} (fun t : ((N).obj (op ⦋0⦌)).I => F.obj.obj
    (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t))))).inv
      (fun t => (Values.CrystallineCechValues.sectionIso p k X Q s F t).inv (y (t 0)))

theorem component_assemble (F : Sheaf J V)
    (y : ∀ i, F.obj.obj (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s i))))
    (t : Fin 1 → ι) :
    Values.CrystallineCechValues.component p k X Q s F (assemble p k X Q s F y) t =
      (Values.CrystallineCechValues.sectionIso p k X Q s F t).inv (y (t 0)) := by
  have h := ModuleCat.piIsoPi_inv_kernel_ι.{u + 1, u, u + 1}
    (fun a : ((N).obj (op ⦋0⦌)).I => F.obj.obj
      (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj a)))) t
  exact congrArg (fun f => f
    (fun a => (Values.CrystallineCechValues.sectionIso p k X Q s F a).inv (y (a 0)))) h

theorem map_component {F G : Sheaf J V} (φ : F ⟶ G)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0) (t : Fin 1 → ι) :
    Values.CrystallineCechValues.component p k X Q s G
        (((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).map φ).f 0 z) t =
      φ.hom.app (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t)))
        (Values.CrystallineCechValues.component p k X Q s F z t) :=
  congrArg (fun f => f z) (Pi.map_π
    (fun a : ((N).obj (op ⦋0⦌)).I => φ.hom.app
      (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj a)))) t)

theorem map_assemble {F G : Sheaf J V} (φ : F ⟶ G)
    (x : G.obj.obj (op Q))
    (y : ∀ i, F.obj.obj (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s i))))
    (hy : ∀ i, φ.hom.app _ (y i) =
      G.obj.map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i)).op x) :
    ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).map φ).f 0
        (assemble p k X Q s F y) =
      (SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s G).f 0 x := by
  apply Concrete.limit_ext (Discrete.functor (fun t : ((N).obj (op ⦋0⦌)).I => G.obj.obj
    (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t)))))
  intro t
  obtain ⟨i, hi⟩ : ∃ i, t.as = fun _ => i := by
    refine ⟨t.as 0, ?_⟩
    funext l
    exact congrArg t.as (@Subsingleton.elim (Fin 1) inferInstance l 0)
  change Values.CrystallineCechValues.component p k X Q s G
    (((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).map φ).f 0 (assemble p k X Q s F y)) t.as =
      Values.CrystallineCechValues.component p k X Q s G
        ((SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s G).f 0 x) t.as
  rw [hi]
  have hn := congrArg (fun f => f (y i)) (φ.hom.naturality
    (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q
      (Values.CrystallineCechValues.singleIso p k X Q s (fun _ => i)).hom).op)
  exact (map_component p k X Q s φ (assemble p k X Q s F y) (fun _ => i)).trans
    ((congrArg (φ.hom.app _) (component_assemble p k X Q s F y (fun _ => i))).trans
      (hn.trans
        ((congrArg (Values.CrystallineCechValues.sectionIso p k X Q s G (fun _ => i)).inv (hy i)).trans
          (Gluing.CrystallineCechGluing.component_augmented p k X Q s G x i).symm)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.CechLift.CrystallineCechLift
