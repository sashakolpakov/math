import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectivePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

/-! # Level Frame Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.LevelFrameParameter

noncomputable section

/-! Requiring selected ordered torsion points of a projective family
to equal the standard frame is represented by an actual closed parameter
scheme. Its point equivalence includes every test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} (Z : Over S) [IsLocallyNoetherian Z.left]
variable {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel n)
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

def fullLevelMarkedProjectivePoint (c : Multiplicative (Fin (2 * g) → ZMod n)) :
    Over.mk (𝟙 Z.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension :=
  Over.homMk (A.fullLevelGlobalSection level c) (A.fullLevelGlobalSection_comp level c) ≫ P.embedding

def normalizedFrameBasisEquation (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (i : Fin (P.dimension + 1)) : Finite.ProperEquationIdeals.ProperFamilyMorphismEquation Z.left where
  source := Over.mk (𝟙 Z.left)
  target := Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension
  proper := by change IsProper (𝟙 Z.left); infer_instance
  flat := by change Flat (𝟙 Z.left); infer_instance
  separated := inferInstance
  lhs := fullLevelMarkedProjectivePoint Z A level P (σ i)
  rhs := Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint Z.left P.dimension i

def normalizedFrameAdditionalEquation (j : Multiplicative (Fin (2 * g) → ZMod n)) :
    Finite.ProperEquationIdeals.ProperFamilyMorphismEquation Z.left where
  source := Over.mk (𝟙 Z.left)
  target := Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension
  proper := by change IsProper (𝟙 Z.left); infer_instance
  flat := by change Flat (𝟙 Z.left); infer_instance
  separated := inferInstance
  lhs := fullLevelMarkedProjectivePoint Z A level P j
  rhs := Scalar.CoordinateProjectivePoints.allOneProjectivePoint Z.left P.dimension

def normalizedFrameEquationList
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) : List (Finite.ProperEquationIdeals.ProperFamilyMorphismEquation Z.left) :=
  normalizedFrameAdditionalEquation Z A level P j :: List.ofFn (normalizedFrameBasisEquation Z A level P σ)

def NormalizedFullLevelFrameAt
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) {T : Scheme.{u}} (c : T ⟶ Z.left) : Prop :=
  (Over.pullback c).map (fullLevelMarkedProjectivePoint Z A level P j) =
      (Over.pullback c).map (Scalar.CoordinateProjectivePoints.allOneProjectivePoint Z.left P.dimension) ∧
    ∀ i, (Over.pullback c).map (fullLevelMarkedProjectivePoint Z A level P (σ i)) =
      (Over.pullback c).map (Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint Z.left P.dimension i)

private theorem forall_cons_ofFn {α : Type*} {n : ℕ}
    (a : α) (f : Fin n → α) (p : α → Prop) :
    (∀ x ∈ a :: List.ofFn f, p x) ↔ p a ∧ ∀ i, p (f i) := by
  constructor
  · intro h
    refine ⟨h _ List.mem_cons_self, fun i => ?_⟩
    exact h _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · rintro ⟨ha, hf⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hf i

omit [IsLocallyNoetherian Z.left] in
theorem normalizedFrameEquationList_test
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) {T : Scheme.{u}} (c : T ⟶ Z.left) :
    (∀ e ∈ normalizedFrameEquationList Z A level P σ j,
      (Over.pullback c).map e.lhs = (Over.pullback c).map e.rhs) ↔
        NormalizedFullLevelFrameAt Z A level P σ j c := by
  have result := forall_cons_ofFn
    (normalizedFrameAdditionalEquation Z A level P j)
    (normalizedFrameBasisEquation Z A level P σ)
    (fun e => (Over.pullback c).map e.lhs = (Over.pullback c).map e.rhs)
  exact result

def normalizedFullLevelFrameParameter
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) : Over S :=
  Finite.ProperEquationParameters.properEquationListParameter Z (normalizedFrameEquationList Z A level P σ j)

def normalizedFullLevelFrameParameterInclusion
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) :
    normalizedFullLevelFrameParameter Z A level P σ j ⟶ Z :=
  Finite.ProperEquationParameters.properEquationListParameterInclusion Z (normalizedFrameEquationList Z A level P σ j)

instance normalizedFullLevelFrameParameterInclusion_closed
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) :
    IsClosedImmersion (normalizedFullLevelFrameParameterInclusion Z A level P σ j).left :=
  inferInstanceAs (IsClosedImmersion
    (Finite.ProperEquationParameters.properEquationListParameterInclusion Z (normalizedFrameEquationList Z A level P σ j)).left)

def normalizedFullLevelFrameParameterPointEquiv
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) (T : Over S) :
    (T ⟶ normalizedFullLevelFrameParameter Z A level P σ j) ≃
      {c : T ⟶ Z // NormalizedFullLevelFrameAt Z A level P σ j c.left} :=
  (Finite.ProperEquationParameters.properEquationListParameterPointEquiv Z (normalizedFrameEquationList Z A level P σ j) T).trans
    { toFun := fun c => ⟨c.val, (normalizedFrameEquationList_test Z A level P σ j c.val.left).mp c.property⟩
      invFun := fun c => ⟨c.val, (normalizedFrameEquationList_test Z A level P σ j c.val.left).mpr c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

def normalizedFullLevelFrameParameterQuasiProjective [IsNoetherian S]
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod n))
    (j : Multiplicative (Fin (2 * g) → ZMod n)) (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation Z) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (normalizedFullLevelFrameParameter Z A level P σ j) :=
  Finite.ProperEquationParameters.properEquationListParameterQuasiProjectivePresentation Z
    (normalizedFrameEquationList Z A level P σ j) Q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.LevelFrameParameter
