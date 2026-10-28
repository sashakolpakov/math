import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.SheafCech

/-! # Sheaf Cech Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafCechAugmentation.CrystallineSheafCechAugmentation

noncomputable section

/-!
# The native restriction augmentation into principal Čech cochains

Sections on the original crystalline object restrict through the actual
principal projections to every intersection of the Čech nerve. These
maps form a cosimplicial transformation, hence a canonical cochain
augmentation natural in the native coefficient sheaf.
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

def cosimplicialFunctor : Sheaf J V ⥤ CosimplicialObject V :=
  CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.coefficients p k X Q ⋙
    FormalCoproduct.cosimplicialObjectFunctor.{u, u, u + 1, u, u + 2} (A := V) N

def restriction (F : Sheaf J V) :
    (Functor.const SimplexCategory).obj (F.obj.obj (op Q)) ⟶
      (cosimplicialFunctor p k X Q s).obj F where
  app n := Pi.lift (fun i => F.obj.map
    (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (((N).obj (op n)).obj i)).op)
  naturality n m f := by
    let En := (N).obj (op n)
    let Em := (N).obj (op m)
    let φ : Em ⟶ En := (N).map f.op
    change 𝟙 _ ≫ (Pi.lift (fun i : Em.I => F.obj.map
      (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (Em.obj i)).op)) =
      (Pi.lift (fun i : En.I => F.obj.map
        (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (En.obj i)).op)) ≫
        Pi.lift (fun i : Em.I => Pi.π _ (φ.f i) ≫
          F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (φ.φ i)).op)
    apply Pi.hom_ext
    intro i
    simp only [Category.id_comp, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    exact (congrArg (fun g => F.obj.map g.op)
      (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k X Q (φ.φ i))).symm.trans
        (F.obj.map_comp _ _)

theorem restriction_cocycle (F : Sheaf J V) :
    (restriction p k X Q s F).app ⦋0⦌ ≫
      ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1 = 0 := by
  let Y := (cosimplicialFunctor p k X Q s).obj F
  let a := restriction p k X Q s F
  change a.app ⦋0⦌ ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Y.map (SimplexCategory.δ i)) = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, Preadditive.comp_add, Preadditive.comp_neg]
  have h0 := a.naturality (SimplexCategory.δ (0 : Fin 2))
  have h1 := a.naturality (SimplexCategory.δ (1 : Fin 2))
  change a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (0 : Fin 2)) at h0
  change a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (1 : Fin 2)) at h1
  rw [← h0, ← h1, add_neg_cancel]

def augmentation (F : Sheaf J V) :
    (CochainComplex.single₀ V).obj (F.obj.obj (op Q)) ⟶
      (CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(restriction p k X Q s F).app ⦋0⦌, restriction_cocycle p k X Q s F⟩

theorem augmentation_natural {F G : Sheaf J V} (f : F ⟶ G) :
    (CochainComplex.single₀ V).map (f.hom.app (op Q)) ≫ augmentation p k X Q s G =
      augmentation p k X Q s F ≫ (CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).map f := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, augmentation, CochainComplex.single₀_map_f_zero]
  let E0 := (N).obj (op ⦋0⦌)
  change f.hom.app (op Q) ≫ (Pi.lift (fun i : E0.I => G.obj.map
      (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (E0.obj i)).op)) =
    (Pi.lift (fun i : E0.I => F.obj.map
      (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (E0.obj i)).op)) ≫
        Limits.Pi.map (fun i : E0.I => f.hom.app
          (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (E0.obj i))))
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
  exact (f.hom.naturality (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (E0.obj i)).op).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafCechAugmentation.CrystallineSheafCechAugmentation
