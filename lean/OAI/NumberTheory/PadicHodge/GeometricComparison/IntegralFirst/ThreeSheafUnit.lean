import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.OpenFormsUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex

/-! # Three Sheaf Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit

noncomputable section

/-! The actual sheafification unit on the first three native de Rham terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

local notation "J" => Opens.grothendieckTopology X.left
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "G" => sheafToPresheaf J (ModuleCat R)

def component : ∀ n, (P).X n ⟶ (((G).mapHomologicalComplex (.up ℕ)).obj K).X n
  | 0 => toSheafify J (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0)
  | 1 => toSheafify J (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 1)
  | 2 => toSheafify J (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 2)
  | _ + 3 => 0

def map : P ⟶ ((G).mapHomologicalComplex (.up ℕ)).obj K where
  f := component R X
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (P).d n (n + 1) = FirstThree.ThreeComplex.FirstThreeComplex.differential (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) n from
      CochainComplex.of_d _ _ n]
    rw [show (((G).mapHomologicalComplex (.up ℕ)).obj K).d n (n + 1) =
        (G).map (FirstThree.ThreeComplex.FirstThreeComplex.differential (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) n) from by
          have hd : (K).d n (n + 1) =
              FirstThree.ThreeComplex.FirstThreeComplex.differential (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) n :=
            CochainComplex.of_d _ _ n
          exact congrArg (G).map hd]
    rcases n with _ | (_ | n)
    · exact (toSheafify_naturality J (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X 0)).symm
    · exact (toSheafify_naturality J (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X 1)).symm
    · change _ ≫ (G).map 0 = 0 ≫ _
      rw [(G).map_zero]
      erw [comp_zero]

theorem high_isIso (n : ℕ) : IsIso ((IntegralFirstThreeSheafUnit.map R X).f (n + 3)) :=
  (isZero_zero (X.left.Opensᵒᵖ ⥤ ModuleCat R)).isIso
    ((G).map_isZero (isZero_zero (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X))) _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit
