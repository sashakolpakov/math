import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionEquivalence

/-! # Family Operation Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyOperationParameters

noncomputable section

/-! Actual quasi-projective parameters for a bounded multiplication, bounded inversion, and a unit point of a fixed proper smooth family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

def overTensorPointEquiv {S : Scheme.{u}} (U V T : Over S) :
    (T ⟶ U ⊗ V) ≃ ((T ⟶ U) × (T ⟶ V)) where
  toFun y := (y ≫ fst U V, y ≫ snd U V)
  invFun p := lift p.1 p.2
  left_inv y := by simp
  right_inv p := by simp

local instance boundedOperationProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance boundedOperationProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)

def boundedFamilyOperationParameter : Over S :=
  (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter jm Pm ⊗ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter ji Pi) ⊗ A

def boundedFamilyOperationParameterQuasiProjectivePresentation (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedFamilyOperationParameter jm ji Pm Pi) :=
  ((HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterQuasiProjectivePresentation jm Pm).product
    (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterQuasiProjectivePresentation ji Pi)).product Q

def boundedFamilyOperationParameterPointEquiv (T : Over S) :
    (T ⟶ boundedFamilyOperationParameter jm ji Pm Pi) ≃
      (((EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor jm Pm).obj (Opposite.op T) ×
        (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor ji Pi).obj (Opposite.op T)) × (T ⟶ A)) :=
  (overTensorPointEquiv _ _ T).trans
    (Equiv.prodCongr ((overTensorPointEquiv _ _ T).trans
      (Equiv.prodCongr (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv jm Pm T)
        (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv ji Pi T))) (Equiv.refl _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyOperationParameters
