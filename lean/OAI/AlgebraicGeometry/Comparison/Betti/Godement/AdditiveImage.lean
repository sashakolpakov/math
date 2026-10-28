import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.ImageBicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column

/-! # Additive Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage

noncomputable section

/-! Forgetting complex scalars retains the actual coefficient maps across direct image. -/

open _root_.CategoryTheory

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

local instance godementAdditiveDirectImageForget : (Complex.SheafForget.Flasque.sheafForget X).Additive :=
  Complex.SheafForget.Flasque.sheafForgetAdditive X

local instance godementAdditiveDirectImagePush : (TopologicalSheafPullback.sheafDirectImage f).Additive :=
  TopologicalSheafPullback.sheafDirectImageAdditive f

local instance godementAdditiveDirectImageAbPush :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

variable {K K' : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ}
  {L L' : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}

def additiveGodementComplexMap (β : K ⟶ K') :
    Cech.additiveGodementComplex K ⟶ Cech.additiveGodementComplex K' :=
  ((Complex.SheafForget.Flasque.sheafForget X).mapHomologicalComplex (.up ℕ)).map β

def additiveDirectImageComplexMap
    (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L) :
    Cech.additiveGodementComplex K ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj
        (Cech.additiveGodementComplex L) :=
  ((Complex.SheafForget.Flasque.sheafForget X).mapHomologicalComplex (.up ℕ)).map α

theorem additiveDirectImageComplexMap_precompose
    (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)
    (β : K' ⟶ K) :
    additiveDirectImageComplexMap f (β ≫ α) =
      additiveGodementComplexMap β ≫ additiveDirectImageComplexMap f α :=
  Functor.map_comp _ _ _

theorem additiveDirectImageComplexMap_postcompose
    (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)
    (β : L ⟶ L') :
    additiveDirectImageComplexMap f
        (α ≫ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).map β) =
      additiveDirectImageComplexMap f α ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
          (additiveGodementComplexMap β) :=
  Functor.map_comp _ _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage
