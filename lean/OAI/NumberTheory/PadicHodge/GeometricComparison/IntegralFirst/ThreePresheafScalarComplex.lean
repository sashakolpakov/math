import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PresheafScalarComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicFormsScalarIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex

/-! # Three Presheaf Scalar Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePresheafScalarComplex.IntegralFirstThreePresheafScalarComplex

noncomputable section

/-! The original native coefficient map acts on the first three presheaf terms and their actual differentials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.scalar R S X
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.preimage R S X Y f

def component : ∀ n, (((F).mapHomologicalComplex (.up ℕ)).obj P).X n ⟶
    (((G).mapHomologicalComplex (.up ℕ)).obj Q).X n
  | 0 => Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h 0
  | 1 => Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h 1
  | 2 => Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h 2
  | _ + 3 => 0

def map : ((F).mapHomologicalComplex (.up ℕ)).obj P ⟶ ((G).mapHomologicalComplex (.up ℕ)).obj Q where
  f := component R S X Y f h
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (((F).mapHomologicalComplex (.up ℕ)).obj P).d n (n + 1) =
        (F).map (FirstThree.ThreeComplex.FirstThreeComplex.differential (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) n) from
          congrArg (F).map (CochainComplex.of_d _ _ n),
      show (((G).mapHomologicalComplex (.up ℕ)).obj Q).d n (n + 1) =
        (G).map (FirstThree.ThreeComplex.FirstThreeComplex.differential (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y) n) from
          congrArg (G).map (CochainComplex.of_d _ _ n)]
    rcases n with _ | (_ | n)
    · exact (Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.differential R S X Y f h 0).symm
    · exact (Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.differential R S X Y f h 1).symm
    · change _ ≫ (G).map 0 = (F).map 0 ≫ _
      rw [(G).map_zero, (F).map_zero]
      erw [comp_zero]

theorem high_isIso (n : ℕ) : IsIso ((IntegralFirstThreePresheafScalarComplex.map R S X Y f h).f (n + 3)) :=
  ((F).map_isZero (isZero_zero (X.left.Opensᵒᵖ ⥤ ModuleCat R))).isIso
    ((G).map_isZero (isZero_zero (Y.left.Opensᵒᵖ ⥤ ModuleCat S))) _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePresheafScalarComplex.IntegralFirstThreePresheafScalarComplex
