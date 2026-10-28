import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Overlaps

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Gluing.CrystallineCechGluing

noncomputable section

/-!
# Degree-zero exactness of native principal Čech cochains

The native sheaf axiom glues the cover-member values of a zero-cocycle.
The singleton intersection identifications then show that its augmentation
is the original cocycle, in the actual categorical product of sections.
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

theorem exists_gluing (F : Sheaf J V) (hs : Ideal.span (Set.range s) = ⊤)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0)
    (hz : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1 z = 0) :
    ∃ x : F.obj.obj (op Q), ∀ i,
      F.obj.map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i)).op x =
        Values.CrystallineCechValues.value p k X Q s F z (fun _ => i) := by
  let F' := (sheafCompose J (forget V)).obj F
  have hF := (isSheaf_iff_isSheaf_of_type J F'.obj).mp F'.property
  have hS := (Presieve.isSheafFor_iff_generate
    (CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve p k X Q ι s)).mpr
      (hF _ (CrystallinePrincipal.Covers.CrystallinePrincipalCovers.covering_mem p k X Q ι s hs))
  rw [CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve, Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨x, hx, _⟩ := hS (fun i => Values.CrystallineCechValues.value p k X Q s F z (fun _ => i))
    (fun i j T f g h => Overlaps.CrystallineCechOverlaps.compatible p k X Q s i j T f g h F z hz)
  exact ⟨x, hx⟩

theorem component_augmented (F : Sheaf J V) (x : F.obj.obj (op Q)) (i : ι) :
    Values.CrystallineCechValues.component p k X Q s F
        ((SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s F).f 0 x) (fun _ => i) =
      (Values.CrystallineCechValues.sectionIso p k X Q s F (fun _ => i)).inv
        (F.obj.map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i)).op x) := by
  have hp := (congrArg (fun f => F.obj.map f.op)
    (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k X Q
      (Values.CrystallineCechValues.singleIso p k X Q s (fun _ => i)).hom)).symm.trans
        (F.obj.map_comp _ _)
  exact (DegreeZero.CrystallineCechDegreeZero.component_restriction p k X Q s F x i).trans
    (congrArg (fun f => f x) hp)

theorem exists_augmentation (F : Sheaf J V) (hs : Ideal.span (Set.range s) = ⊤)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0)
    (hz : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1 z = 0) :
    ∃ x : F.obj.obj (op Q),
      (SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s F).f 0 x = z := by
  obtain ⟨x, hx⟩ := exists_gluing p k X Q s F hs z hz
  refine ⟨x, ?_⟩
  apply Concrete.limit_ext (Discrete.functor (fun t : ((N).obj (op ⦋0⦌)).I => F.obj.obj
    (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋0⦌)).obj t)))))
  intro t
  obtain ⟨i, hi⟩ : ∃ i, t.as = fun _ => i := by
    refine ⟨t.as 0, ?_⟩
    funext l
    exact congrArg t.as (@Subsingleton.elim (Fin 1) inferInstance l 0)
  change Values.CrystallineCechValues.component p k X Q s F
    ((SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s F).f 0 x) t.as =
      Values.CrystallineCechValues.component p k X Q s F z t.as
  rw [hi]
  exact (component_augmented p k X Q s F x i).trans
    ((congrArg (Values.CrystallineCechValues.sectionIso p k X Q s F (fun _ => i)).inv (hx i)).trans
      (Values.CrystallineCechValues.recover_component p k X Q s F z (fun _ => i)))

def augmentedShortComplex (F : Sheaf J V) : ShortComplex V :=
  ShortComplex.mk ((SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s F).f 0)
    (((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1)
    (SheafCechAugmentation.CrystallineSheafCechAugmentation.restriction_cocycle p k X Q s F)

theorem augmented_exact (F : Sheaf J V) (hs : Ideal.span (Set.range s) = ⊤) :
    (augmentedShortComplex p k X Q s F).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  exact exists_augmentation p k X Q s F hs z hz

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Gluing.CrystallineCechGluing
