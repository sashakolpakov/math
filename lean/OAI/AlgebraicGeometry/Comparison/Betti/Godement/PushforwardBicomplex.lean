import OAI.AlgebraicGeometry.Comparison.Betti.Godement.ImageBicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.Total
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Pushforward Bicomplex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardBicomplex

noncomputable section

/-! The canonical relative Godement maps act in both degrees of the actual bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

local instance godementTotalNativePreadditive (Z : TopCat.{0}) :
    Preadditive (TopCat.Sheaf (ModuleCat.{0} ℂ) Z) :=
  inferInstanceAs (Preadditive (ConstantSheafSections.ComplexSheaves Z))

local instance godementTotalNativeFiniteBiproducts (Z : TopCat.{0}) :
    HasFiniteBiproducts (TopCat.Sheaf (ModuleCat.{0} ℂ) Z) where
  out _ := ⟨fun G => HasBiproduct.of_hasProduct G⟩

local instance godementTotalNativeFiniteCoproducts (Z : TopCat.{0}) :
    HasFiniteCoproducts (TopCat.Sheaf (ModuleCat.{0} ℂ) Z) :=
  hasFiniteCoproducts_of_hasFiniteBiproducts (TopCat.Sheaf (ModuleCat.{0} ℂ) Z)

local instance godementBicomplexDirectImageAdditive : (TopologicalSheafPullback.sheafDirectImage f).Additive :=
  TopologicalSheafPullback.sheafDirectImageAdditive f

variable {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ}
  {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

def godementDirectImageTotalMap : Bicomplex.godementTotal K ⟶
    ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj (Bicomplex.godementTotal L) :=
  total.map (ImageBicomplex.godementDirectImageBicomplexMap f α) (.up ℕ) ≫
    @Finite.Total.totalComparison _ _ _ _ _ _ _ _ (TopologicalSheafPullback.sheafDirectImage f)
      (TopologicalSheafPullback.sheafDirectImageAdditive f) (Bicomplex.godementBicomplex Y L)

theorem godementDirectImageTotalMap_augmentation :
    Bicomplex.godementTotalAugmentation K ≫ godementDirectImageTotalMap f α =
      α ≫ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).map (Bicomplex.godementTotalAugmentation L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  let B := Bicomplex.godementBicomplex X K
  let C := ImageBicomplex.godementDirectImageBicomplex f L
  let D := Bicomplex.godementBicomplex Y L
  let F := TopologicalSheafPullback.sheafDirectImage f
  let φ : B ⟶ C := ImageBicomplex.godementDirectImageBicomplexMap f α
  have hB : B.HasTotal (.up ℕ) :=
    @TotalExists.hasTotal_of_finiteCoproducts (ConstantSheafSections.ComplexSheaves X) _
      (godementTotalNativePreadditive X) (godementTotalNativeFiniteCoproducts X) B
  have hC : C.HasTotal (.up ℕ) :=
    @TotalExists.hasTotal_of_finiteCoproducts (ConstantSheafSections.ComplexSheaves X) _
      (godementTotalNativePreadditive X) (godementTotalNativeFiniteCoproducts X) C
  have hD : D.HasTotal (.up ℕ) :=
    @TotalExists.hasTotal_of_finiteCoproducts (ConstantSheafSections.ComplexSheaves Y) _
      (godementTotalNativePreadditive Y) (godementTotalNativeFiniteCoproducts Y) D
  let t := @Finite.Total.totalComparisonComponent _ _ _ _ _ _ _ _ (TopologicalSheafPullback.sheafDirectImage f)
    (TopologicalSheafPullback.sheafDirectImageAdditive f) (Bicomplex.godementBicomplex Y L) n
  have hu : (Functor.stalkFamilyUnit X).app (K.X n) ≫ (φ.f n).f 0 =
      α.f n ≫ F.map ((Functor.stalkFamilyUnit Y).app (L.X n)) :=
    PushforwardResolution.godementRelativeResolutionMap_augmentation f (α.f n)
  have ht :=
    @Finite.Total.ι_totalComparisonComponent _ _ _ _ _ _ _ _ (TopologicalSheafPullback.sheafDirectImage f)
      (TopologicalSheafPullback.sheafDirectImageAdditive f) (Bicomplex.godementBicomplex Y L) n 0 n rfl
  change ((Functor.stalkFamilyUnit X).app (K.X n) ≫ B.ιTotal (.up ℕ) n 0 n rfl) ≫
      ((total.map φ (.up ℕ)).f n ≫ t) =
    α.f n ≫ F.map ((Functor.stalkFamilyUnit Y).app (L.X n) ≫ D.ιTotal (.up ℕ) n 0 n rfl)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ t) (Category.assoc _ _ _)).trans
      ((congrArg (fun a => ((Functor.stalkFamilyUnit X).app (K.X n) ≫ a) ≫ t)
        (ιTotal_map B C φ (.up ℕ) n 0 n rfl)).trans
        ((congrArg (· ≫ t) (Category.assoc _ _ _).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg₂ (· ≫ ·) hu ht).trans
              ((Category.assoc _ _ _).trans
                (congrArg (α.f n ≫ ·) (F.map_comp _ _).symm)))))))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardBicomplex
