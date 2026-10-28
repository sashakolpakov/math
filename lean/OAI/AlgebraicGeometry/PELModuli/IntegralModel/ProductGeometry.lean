import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseTopology
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Product

/-! # Product Geometry -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductGeometry

noncomputable section

/-! Actual finite scheme products and their analytic connectedness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

def piZeroIso {B : Scheme} (X : Fin 0 → Over B) : ∏ᶜ X ≅ 𝟙_ (Over B) where
  hom := toUnit _
  inv := Pi.lift (fun i => Fin.elim0 i)
  hom_inv_id := by apply Pi.hom_ext; intro i; exact Fin.elim0 i
  inv_hom_id := Subsingleton.elim _ _

def piSuccIso {B : Scheme} {n : ℕ} (X : Fin (n + 1) → Over B) :
    ∏ᶜ X ≅ X 0 ⊗ ∏ᶜ (fun i : Fin n => X i.succ) where
  hom := lift (Pi.π X 0) (Pi.lift (fun i : Fin n => Pi.π X i.succ))
  inv := Pi.lift (Fin.cases (fst _ _) (fun i => snd _ _ ≫ Pi.π _ i))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  inv_hom_id := by
    apply hom_ext
    · simp
    · apply Pi.hom_ext
      intro i
      simp

def schemePointsHomeomorph {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (e : X ≅ Y) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y :=
  TopCat.homeoOfIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.mapIso e)

theorem points_pathConnected_of_iso {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (e : X ≅ Y)
    [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] :
    PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  (schemePointsHomeomorph e).symm.surjective.pathConnectedSpace
    (schemePointsHomeomorph e).symm.continuous

theorem unitPoints_pathConnected :
    PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase))) := by
  let : Subsingleton (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase))) :=
    inferInstanceAs (Subsingleton (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)))
  let : Nonempty (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase))) := ⟨𝟙 _⟩
  infer_instance

theorem piPoints_pathConnected (n : ℕ) (X : Fin n → Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [∀ i, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X i))] :
    PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (∏ᶜ X)) := by
  induction n with
  | zero =>
    let : PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase))) :=
      unitPoints_pathConnected
    exact points_pathConnected_of_iso (piZeroIso X)
  | succ n ih =>
    let : PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (∏ᶜ (fun i : Fin n => X i.succ))) :=
      ih (fun i => X i.succ)
    let : PathConnectedSpace
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X 0 ⊗ ∏ᶜ (fun i : Fin n => X i.succ))) :=
      AlbaneseTopology.schemeProductPoints_pathConnected _ _
    exact points_pathConnected_of_iso (piSuccIso X)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductGeometry
