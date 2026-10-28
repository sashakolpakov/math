import OAI.AlgebraicGeometry.SheafCohomology.Cech.Resolution
import OAI.AlgebraicGeometry.SheafCohomology.Cech.FormalCoproductAdditive

/-! # Cech Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechFunctor

noncomputable section

/-! The existing actual sheaf Čech resolutions form an additive functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}

def sheafCechFactorMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechFactorPresheaf F ⟶ SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechFactorPresheaf G where
  app A := (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat A.unop.isOpenEmbedding ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat A.unop.inclusion').map f
  naturality A B h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact f.hom.naturality _

def sheafCechFactorFunctor : TopCat.Sheaf AddCommGrpCat.{u} X ⥤
    (Opens X)ᵒᵖ ⥤ TopCat.Sheaf AddCommGrpCat.{u} X where
  obj F := SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechFactorPresheaf F
  map f := sheafCechFactorMap f
  map_id F := by
    ext A
    rfl
  map_comp f g := by
    ext A
    rfl

instance sheafCechFactorFunctor_additive : (sheafCechFactorFunctor (X := X)).Additive where
  map_add := by
    intro F G f g
    ext A
    rfl

def sheafCechResolutionFunctor {ι : Type u} (U : ι → Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  sheafCechFactorFunctor ⋙ cechComplexFunctor U

instance sheafCechResolutionFunctor_additive {ι : Type u} (U : ι → Opens X) :
    (sheafCechResolutionFunctor U).Additive where
  map_add := by
    intro F G f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply Pi.hom_ext
    intro i
    change Fin (n + 1) → ι at i
    change (Limits.Pi.map (fun j : Fin (n + 1) → ι =>
        (sheafCechFactorMap (f + g)).app (op (∏ᶜ fun k => U (j k)))) ≫ Pi.π _ i) =
      (Limits.Pi.map (fun j : Fin (n + 1) → ι =>
        (sheafCechFactorMap f).app (op (∏ᶜ fun k => U (j k)))) +
        Limits.Pi.map (fun j : Fin (n + 1) → ι =>
          (sheafCechFactorMap g).app (op (∏ᶜ fun k => U (j k))))) ≫ Pi.π _ i
    simp only [Pi.map_π, Preadditive.add_comp]
    rfl

theorem sheafCechResolutionFunctor_obj {ι : Type u} (U : ι → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (sheafCechResolutionFunctor U).obj F = SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex F U := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechFunctor
