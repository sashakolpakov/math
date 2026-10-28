import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeFrameAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.Stabilizer

/-! # Real Special Linear Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RealSpecialLinearCoordinates.Construction

noncomputable section

section

/-! Determinant-one real representations in special-linear matrix
coordinates, compatible with the lattice-frame action of Mahler's
compactness criterion. -/

open scoped Classical
open _root_.Module

def realSpecialLinearCoordinates
    {H E : Type*} [Group H] [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (ρ : H →* (E ≃ₗ[ℝ] E)) (hρ : ∀ g, (ρ g).toLinearMap.det = 1)
    (b : Basis (Fin m) ℝ E) : H →* Algebraic.SL m ℝ where
  toFun g := ⟨LinearMap.toMatrix b b (ρ g).toLinearMap, by
    rw [LinearMap.det_toMatrix]
    exact hρ g⟩
  map_one' := by
    apply Subtype.ext
    change LinearMap.toMatrix b b (ρ 1).toLinearMap = 1
    rw [map_one]
    exact LinearMap.toMatrix_id b
  map_mul' g h := by
    apply Subtype.ext
    change LinearMap.toMatrix b b (ρ (g * h)).toLinearMap =
      LinearMap.toMatrix b b (ρ g).toLinearMap * LinearMap.toMatrix b b (ρ h).toLinearMap
    rw [map_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

theorem realSpecialLinearCoordinates_frame_action
    {H E : Type*} [Group H] [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (ρ : H →* (E ≃ₗ[ℝ] E)) (hρ : ∀ g, (ρ g).toLinearMap.det = 1)
    (b : Basis (Fin m) ℝ E) (g : H) :
    LatticeFrameAction.Construction.matrixFrameAction b (realSpecialLinearCoordinates ρ hρ b g).toGL = ρ g := by
  apply LinearEquiv.toLinearMap_injective
  rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap]
  change Matrix.toLin b b (LinearMap.toMatrix b b (ρ g).toLinearMap) = (ρ g).toLinearMap
  exact Matrix.toLin_toMatrix b b (ρ g).toLinearMap

theorem realSpecialLinearCoordinates_injective
    {H E : Type*} [Group H] [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (ρ : H →* (E ≃ₗ[ℝ] E)) (hρ : ∀ g, (ρ g).toLinearMap.det = 1)
    (b : Basis (Fin m) ℝ E) (hinj : Function.Injective ρ) :
    Function.Injective (realSpecialLinearCoordinates ρ hρ b) := by
  intro g h he
  apply hinj
  rw [← realSpecialLinearCoordinates_frame_action ρ hρ b g,
    ← realSpecialLinearCoordinates_frame_action ρ hρ b h, he]

theorem continuous_realSpecialLinearCoordinates
    {H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (ρ : H →* (E ≃ₗ[ℝ] E)) (hρ : ∀ g, (ρ g).toLinearMap.det = 1)
    (b : Basis (Fin m) ℝ E) (hcont : Continuous (fun a : H × E => ρ a.1 a.2)) :
    Continuous (realSpecialLinearCoordinates ρ hρ b) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [LinearMap.toMatrix_apply']
  change Continuous (fun g => b.coord i (ρ g (b j)))
  exact (b.coord i).continuous_of_finiteDimensional.comp
    (hcont.comp (continuous_id.prodMk continuous_const))

end

/-! The real special-linear action on a chosen vector-space frame is
jointly continuous and faithful. -/

open scoped Classical
open _root_.Module

def specialFrameRepresentation
    {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ} (b : Basis (Fin m) ℝ E) :
    Algebraic.SL m ℝ →* (E ≃ₗ[ℝ] E) :=
  (LatticeFrameAction.Construction.matrixFrameAction b).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL

theorem specialFrameRepresentation_injective
    {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ} (b : Basis (Fin m) ℝ E) :
    Function.Injective (specialFrameRepresentation b) :=
  (LatticeFrameAction.Construction.matrixFrameAction b).injective.comp Matrix.SpecialLinearGroup.toGL_injective

theorem continuous_specialFrameRepresentation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (b : Basis (Fin m) ℝ E) :
    Continuous (fun a : Algebraic.SL m ℝ × E => specialFrameRepresentation b a.1 a.2) := by
  have he (g : Algebraic.SL m ℝ) (x : E) : specialFrameRepresentation b g x =
      b.equivFun.symm ((g : Matrix (Fin m) (Fin m) ℝ).mulVec (b.equivFun x)) := by
    apply b.equivFun.injective
    rw [b.equivFun.apply_symm_apply, Basis.equivFun_apply]
    change (b.repr ((LatticeFrameAction.Construction.matrixFrameAction b g.toGL).toLinearMap x) : Fin m → ℝ) = _
    rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap]
    exact Matrix.repr_toLin b b _ x
  simp_rw [he]
  apply b.equivFun.symm.continuous_of_finiteDimensional.comp
  exact (continuous_subtype_val.comp continuous_fst).matrix_mulVec
    (b.equivFun.continuous_of_finiteDimensional.comp continuous_snd)

theorem mem_realSpecialLinearCoordinates_range_iff
    {H E : Type*} [Group H] [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (ρ : H →* (E ≃ₗ[ℝ] E)) (hρ : ∀ g, (ρ g).toLinearMap.det = 1)
    (b : Basis (Fin m) ℝ E) (g : Algebraic.SL m ℝ) :
    g ∈ (realSpecialLinearCoordinates ρ hρ b).range ↔
      ∃ h, ρ h = specialFrameRepresentation b g := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, (realSpecialLinearCoordinates_frame_action ρ hρ b h).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    apply specialFrameRepresentation_injective b
    exact (realSpecialLinearCoordinates_frame_action ρ hρ b h).trans hh

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RealSpecialLinearCoordinates.Construction
