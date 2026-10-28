import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge

/-! # Cech Augmentation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechAugmentation

noncomputable section

/-! The actual Čech augmentation extends from sheaves to complexes of sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

theorem sheafCechAugmentation_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    f ≫ SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation G U =
      SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation F U ≫ ((CechFunctor.sheafCechResolutionFunctor U).map f).f 0 := by
  apply Pi.hom_ext
  intro i
  change Fin 1 → ι at i
  let A := ∏ᶜ fun k : Fin 1 => U (i k)
  let aF := SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation F U
  let aG := SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation G U
  let pF := Pi.π (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermFactor F U 0) i
  let pG := Pi.π (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermFactor G U 0) i
  let m := ((CechFunctor.sheafCechResolutionFunctor U).map f).f 0
  let t := (CechFunctor.sheafCechFactorMap f).app (op A)
  have hF : aF ≫ pF = (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.toRestrict AddCommGrpCat A).app F := Pi.lift_comp_π _ i
  have hG : aG ≫ pG = (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.toRestrict AddCommGrpCat A).app G := Pi.lift_comp_π _ i
  have hm : m ≫ pG = pF ≫ t :=
    Pi.map_π (fun j : Fin 1 → ι =>
      (CechFunctor.sheafCechFactorMap f).app (op (∏ᶜ fun k => U (j k)))) i
  have hn : f ≫ (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.toRestrict AddCommGrpCat A).app G =
      (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.toRestrict AddCommGrpCat A).app F ≫ t :=
    (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.toRestrict AddCommGrpCat A).naturality f
  exact (Category.assoc f aG pG).trans ((congrArg (fun z => f ≫ z) hG).trans
    (hn.trans ((congrArg (fun z => z ≫ t) hF.symm).trans
      ((Category.assoc aF pF t).trans ((congrArg (fun z => aF ≫ z) hm.symm).trans
        (Category.assoc aF m pG).symm)))))

def sheafCechBicomplex (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) :
    HomologicalComplex₂ (TopCat.Sheaf AddCommGrpCat.{u} X) (.up ℕ) (.up ℕ) :=
  ((CechFunctor.sheafCechResolutionFunctor U).mapHomologicalComplex (.up ℕ)).obj K

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)

def sheafCechComplexAugmentation (q : ℕ) :
    K.X q ⟶ ((CechAugmentation.sheafCechBicomplex U K).X q).X 0 :=
  SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation (K.X q) U

theorem sheafCechComplexAugmentation_comm (q q' : ℕ) :
    sheafCechComplexAugmentation U K q ≫ ((CechAugmentation.sheafCechBicomplex U K).d q q').f 0 =
      K.d q q' ≫ sheafCechComplexAugmentation U K q' :=
  (sheafCechAugmentation_naturality U (K.d q q')).symm

theorem sheafCechComplexAugmentation_comp_d (q : ℕ) :
    sheafCechComplexAugmentation U K q ≫ ((CechAugmentation.sheafCechBicomplex U K).X q).d 0 1 = 0 := by
  change SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation (K.X q) U ≫ (SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex (K.X q) U).d 0 1 = 0
  rw [SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex_d]
  exact SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation_comp (K.X q) U

def sheafCechResolutionEdge : K ⟶ (CechAugmentation.sheafCechBicomplex U K).total (.up ℕ) :=
  (SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (sheafCechBicomplex U K)) K
    (sheafCechComplexAugmentation U K)
    (fun q q' _ => sheafCechComplexAugmentation_comm U K q q')
    (sheafCechComplexAugmentation_comp_d U K)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechAugmentation
