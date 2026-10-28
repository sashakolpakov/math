import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Geometric Frame -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricFrame

noncomputable section

/-! The displayed geometric Hodge frame is a linear embedding, with
its stated coordinate extraction as an actual left inverse. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def geometricFrameLinear (z : BallNatural.Ball) : (BallGeometryData.FrameIndex A → ℂ) →ₗ[ℂ] BallGeometryData.ComplexPhase A where
  toFun := BallGeometryData.geometricFrame A z
  map_add' a b := by
    funext v
    apply Prod.ext <;> funext ij <;> dsimp [BallGeometryData.geometricFrame]
    all_goals split_ifs <;> ring
  map_smul' c a := by
    funext v
    apply Prod.ext <;> funext ij <;> dsimp [BallGeometryData.geometricFrame]
    all_goals split_ifs <;> ring

def geometricCoordinateLinear : BallGeometryData.ComplexPhase A →ₗ[ℂ] (BallGeometryData.FrameIndex A → ℂ) where
  toFun := BallGeometryData.geometricCoordinates A
  map_add' a b := by
    funext i
    dsimp [BallGeometryData.geometricCoordinates]
    split_ifs <;> rfl
  map_smul' c a := by
    funext i
    dsimp [BallGeometryData.geometricCoordinates]
    split_ifs <;> rfl

theorem geometric_coordinates_frame (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) :
    BallGeometryData.geometricCoordinates A (BallGeometryData.geometricFrame A z a) = a := by
  funext i
  rcases i with ⟨v, i, j⟩
  by_cases hv : v = A.distinguished
  · subst v
    fin_cases i <;> simp [BallGeometryData.geometricCoordinates, BallGeometryData.geometricFrame, DeterminantCoordinates.lineVector, DeterminantCoordinates.annihilatorVector]
  · by_cases hp : A.positive v j
    · simp [BallGeometryData.geometricCoordinates, BallGeometryData.geometricFrame, hv, hp]
    · simp [BallGeometryData.geometricCoordinates, BallGeometryData.geometricFrame, hv, hp]

theorem geometricFrame_injective (z : BallNatural.Ball) : Function.Injective (BallGeometryData.geometricFrame A z) := by
  intro a b h
  have he := congrArg (BallGeometryData.geometricCoordinates A) h
  simpa only [geometric_coordinates_frame] using he

theorem geometricFrame_range (z : BallNatural.Ball) :
    ((geometricFrameLinear A z).range : Set (BallGeometryData.ComplexPhase A)) =
      {w : BallGeometryData.ComplexPhase A | BallGeometryData.geometricFrame A z (BallGeometryData.geometricCoordinates A w) = w} := by
  ext w
  constructor
  · rintro ⟨a, rfl⟩
    exact congrArg (BallGeometryData.geometricFrame A z) (geometric_coordinates_frame A z a)
  · intro hw
    exact ⟨BallGeometryData.geometricCoordinates A w, hw⟩

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricFrame
