import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SingleZero
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorFlip

/-! # Permutation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Permutation

noncomputable section

/-! Symmetry and permutations of the native total tensor complexes,
including the common total complex for the two iterated Tor computations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R]

local instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{0} R) ℤ)
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R ⥤ ModuleCat.{0} R)
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms] :
    HomologicalComplex.HasMapBifunctor P Q F (.up ℤ) := by
  intro n
  infer_instance

local instance goodTensor₁₂ (P Q S : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.HasGoodTensor₁₂ P Q S := by
  intro i j
  exact CategoryTheory.Limits.preservesColimit_of_natIso _
    (BraidedCategory.tensorLeftIsoTensorRight (S.X j))

local instance goodTensor₂₃ (P Q S : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.HasGoodTensor₂₃ P Q S := by
  intro i j
  infer_instance

def doubleBraidingIso (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    (((curriedTensor (ModuleCat.{0} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj Q ≅
      ((((curriedTensor (ModuleCat.{0} R)).flip).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj Q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (NatIso.mapHomologicalComplex
      ((BraidedCategory.curriedBraidingNatIso (ModuleCat.{0} R)).app (P.X i)) (.up ℤ)).app Q) (fun i j _ => by
        apply HomologicalComplex.Hom.ext
        funext k
        exact (NatTrans.congr_app
          ((BraidedCategory.curriedBraidingNatIso (ModuleCat.{0} R)).hom.naturality (P.d i j)) (Q.X k)).symm)

def braiding (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.tensorObj P Q ≅ HomologicalComplex.tensorObj Q P :=
  HomologicalComplex₂.total.mapIso (doubleBraidingIso R P Q) (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso Q P (curriedTensor (ModuleCat.{0} R)) (.up ℤ)

def swapOuter (L N P : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.tensorObj L (HomologicalComplex.tensorObj N P) ≅
      HomologicalComplex.tensorObj P (HomologicalComplex.tensorObj N L) :=
  (HomologicalComplex.associator L N P).symm ≪≫
    braiding R (HomologicalComplex.tensorObj L N) P ≪≫
      ((curriedTensor (ModuleCat.{0} R)).map₂CochainComplex.obj P).mapIso (braiding R L N)

def moduleMiddle (M : ModuleCat.{0} R) (P L : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.tensorObj L (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P) ≅
      HomologicalComplex.tensorObj P (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj L) :=
  ((curriedTensor (ModuleCat.{0} R)).map₂CochainComplex.obj L).mapIso
    (SingleZero.iso R M P).symm ≪≫
      swapOuter R L (SingleZero.singleZero R M) P ≪≫
      ((curriedTensor (ModuleCat.{0} R)).map₂CochainComplex.obj P).mapIso (SingleZero.iso R M L)

def moduleMiddleHomology (M : ModuleCat.{0} R) (P L : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ) :
    (HomologicalComplex.tensorObj L (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P)).homology n ≅
      (HomologicalComplex.tensorObj P (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj L)).homology n :=
  HomologicalComplex.homologyMapIso (moduleMiddle R M P L) n

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Permutation
