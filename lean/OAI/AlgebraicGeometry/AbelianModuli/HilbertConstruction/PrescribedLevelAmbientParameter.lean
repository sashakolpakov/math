import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.LevelFrameParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Prescribed Level Ambient Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedLevelAmbientParameter

noncomputable section

/-! The closed locus where every prescribed full-level point equals its
specified point in the original projective ambient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} (Z : Over S) [IsLocallyNoetherian Z.left]
variable {g N m : ℕ} (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N)
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
variable (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
variable (q : Fin m → (Over.mk (𝟙 Z.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension))

def prescribedFullLevelAmbientEquation (k : Fin m) : Finite.ProperEquationIdeals.ProperFamilyMorphismEquation Z.left where
  source := Over.mk (𝟙 Z.left)
  target := Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension
  proper := inferInstanceAs (IsProper (𝟙 Z.left))
  flat := inferInstanceAs (Flat (𝟙 Z.left))
  separated := inferInstance
  lhs := Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P (labels k)
  rhs := q k

def prescribedFullLevelAmbientEquations : List (Finite.ProperEquationIdeals.ProperFamilyMorphismEquation Z.left) :=
  List.ofFn (prescribedFullLevelAmbientEquation Z A level P labels q)

def PrescribedFullLevelAmbientAt {T : Scheme.{u}} (c : T ⟶ Z.left) : Prop :=
  ∀ k, (Over.pullback c).map (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P (labels k)) =
    (Over.pullback c).map (q k)

omit [IsLocallyNoetherian Z.left] in
theorem prescribedFullLevelAmbientEquations_test {T : Scheme.{u}} (c : T ⟶ Z.left) :
    (∀ e ∈ prescribedFullLevelAmbientEquations Z A level P labels q,
      (Over.pullback c).map e.lhs = (Over.pullback c).map e.rhs) ↔
      PrescribedFullLevelAmbientAt Z A level P labels q c := by
  simp only [prescribedFullLevelAmbientEquations, List.forall_mem_ofFn_iff]
  rfl

def prescribedFullLevelAmbientParameter : Over S :=
  Finite.ProperEquationParameters.properEquationListParameter Z (prescribedFullLevelAmbientEquations Z A level P labels q)

def prescribedFullLevelAmbientParameterInclusion :
    prescribedFullLevelAmbientParameter Z A level P labels q ⟶ Z :=
  Finite.ProperEquationParameters.properEquationListParameterInclusion Z (prescribedFullLevelAmbientEquations Z A level P labels q)

instance prescribedFullLevelAmbientParameterInclusion_closed :
    IsClosedImmersion (prescribedFullLevelAmbientParameterInclusion Z A level P labels q).left :=
  Finite.ProperEquationParameters.properEquationListParameterInclusion_closed Z (prescribedFullLevelAmbientEquations Z A level P labels q)

def prescribedFullLevelAmbientParameterPointEquiv (T : Over S) :
    (T ⟶ prescribedFullLevelAmbientParameter Z A level P labels q) ≃
      {c : T ⟶ Z // PrescribedFullLevelAmbientAt Z A level P labels q c.left} :=
  (Finite.ProperEquationParameters.properEquationListParameterPointEquiv Z (prescribedFullLevelAmbientEquations Z A level P labels q) T).trans
    { toFun := fun c => ⟨c.val, (prescribedFullLevelAmbientEquations_test
        Z A level P labels q c.val.left).mp c.property⟩
      invFun := fun c => ⟨c.val, (prescribedFullLevelAmbientEquations_test
        Z A level P labels q c.val.left).mpr c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

def prescribedFullLevelAmbientParameterQuasiProjective
    [IsNoetherian S] (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation Z) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (prescribedFullLevelAmbientParameter Z A level P labels q) :=
  Finite.ProperEquationParameters.properEquationListParameterQuasiProjectivePresentation Z
    (prescribedFullLevelAmbientEquations Z A level P labels q) Q

def prescribedFullLevelAmbientUniversalFamily :
    Level.Data.AbelianSchemeWithFullLevel g N (prescribedFullLevelAmbientParameter Z A level P labels q).left where
  abelian := A.pullback (prescribedFullLevelAmbientParameterInclusion Z A level P labels q).left
  level := level.pullback (prescribedFullLevelAmbientParameterInclusion Z A level P labels q).left

def prescribedFullLevelAmbientUniversalProjectivePresentation :
    Projective.ProjectivePresentations.ProjectivePresentation (prescribedFullLevelAmbientUniversalFamily Z A level P labels q).abelian.scheme :=
  P.baseChange (prescribedFullLevelAmbientParameterInclusion Z A level P labels q).left

theorem prescribedFullLevelAmbientParameter_universal :
    PrescribedFullLevelAmbientAt Z A level P labels q
      (prescribedFullLevelAmbientParameterInclusion Z A level P labels q).left :=
  (prescribedFullLevelAmbientEquations_test Z A level P labels q _).mp
    (Finite.ProperEquationParameters.properEquationListParameter_universal Z (prescribedFullLevelAmbientEquations Z A level P labels q))

omit [IsLocallyNoetherian Z.left] in
theorem prescribedFullLevelAmbientAt_reindex (e : Fin m ≃ Fin m) {T : Scheme.{u}} (c : T ⟶ Z.left) :
    PrescribedFullLevelAmbientAt Z A level P (e.trans labels) (q ∘ e) c ↔
      PrescribedFullLevelAmbientAt Z A level P labels q c := by
  constructor
  · intro h k
    simpa only [Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply] using h (e.symm k)
  · intro h k
    exact h (e k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedLevelAmbientParameter
