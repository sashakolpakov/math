import OAI.ArithmeticGeometry.Models.Foundations
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Descent -/

namespace OAI.ArithmeticGeometry.Models.Descent.Constructions.Foundations

/-! Expansion of a fixed model through larger finite coefficient rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
variable (s : Finset K) (X : Over (CoefficientSystem.Constructions.Foundations.coefficientBase R K s))

/-- All enlargements of the coefficient base, pulled back to the fixed model. -/
noncomputable def expansionOverDiagram :
    Over (op s) ⥤ Over X.left :=
  Over.post (X := op s) (CoefficientSystem.Constructions.Foundations.coefficientSchemeDiagram R K) ⋙ Over.pullback X.hom

noncomputable def expansionOverCone : Cone (expansionOverDiagram R K s X) :=
  (Over.pullback X.hom).mapCone
    ((Over.conePost (CoefficientSystem.Constructions.Foundations.coefficientSchemeDiagram R K) (op s)).obj
      (CoefficientSystem.Constructions.Foundations.coefficientSchemeCone R K))

noncomputable def expansionOverConeIsLimit : IsLimit (expansionOverCone R K s X) := by
  classical
  let D : Over (op s) ⥤ Over (CoefficientSystem.Constructions.Foundations.coefficientBase R K s) :=
    Over.post (X := op s) (CoefficientSystem.Constructions.Foundations.coefficientSchemeDiagram R K)
  let c : Cone D := (Over.conePost (CoefficientSystem.Constructions.Foundations.coefficientSchemeDiagram R K) (op s)).obj
    (CoefficientSystem.Constructions.Foundations.coefficientSchemeCone R K)
  have hc : IsLimit c := Over.isLimitConePost (op s) (CoefficientSystem.Constructions.Foundations.coefficientSchemeConeIsLimit R K)
  let : PreservesLimit D (Over.pullback X.hom) :=
    (Over.mapPullbackAdj X.hom).rightAdjoint_preservesLimits.preservesLimitsOfShape.preservesLimit
  exact isLimitOfPreserves (Over.pullback X.hom) hc

noncomputable def expansionDiagram : Over (op s) ⥤ Scheme.{u} :=
  expansionOverDiagram R K s X ⋙ Over.forget X.left

noncomputable def expansionCone : Cone (expansionDiagram R K s X) :=
  (Over.forget X.left).mapCone (expansionOverCone R K s X)

noncomputable def expansionConeIsLimit : IsLimit (expansionCone R K s X) := by
  classical
  exact isLimitOfPreserves (Over.forget X.left) (expansionOverConeIsLimit R K s X)

theorem expansion_structure_affine (i : Over (op s)) :
    IsAffineHom ((expansionOverDiagram R K s X).obj i).hom := by
  change IsAffineHom
    (pullback.snd (CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (leOfHom i.hom.unop)) X.hom)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback _ _) inferInstance

theorem expansion_transition_affine {i j : Over (op s)} (f : i ⟶ j) :
    IsAffineHom ((expansionDiagram R K s X).map f) := by
  let : IsAffineHom ((expansionOverDiagram R K s X).obj j).hom :=
    expansion_structure_affine R K s X j
  change IsAffineHom ((expansionOverDiagram R K s X).map f).left
  let : IsAffineHom (((expansionOverDiagram R K s X).map f).left ≫
      ((expansionOverDiagram R K s X).obj j).hom) := by
    rw [((expansionOverDiagram R K s X).map f).w]
    exact expansion_structure_affine R K s X i
  exact IsAffineHom.of_comp _ ((expansionOverDiagram R K s X).obj j).hom

theorem expansion_compact [QuasiCompact X.hom] (i : Over (op s)) :
    CompactSpace ((expansionDiagram R K s X).obj i) := by
  change CompactSpace (pullback (C := Scheme) (CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (leOfHom i.hom.unop)) X.hom)
  infer_instance

theorem expansion_quasiSeparated [QuasiSeparated X.hom] (i : Over (op s)) :
    QuasiSeparatedSpace ((expansionDiagram R K s X).obj i) := by
  change QuasiSeparatedSpace
    (pullback (C := Scheme) (CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (leOfHom i.hom.unop)) X.hom)
  apply quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ X.hom)

/-- The structure maps to the original coefficient base. -/
noncomputable def expansionToBase :
    expansionDiagram R K s X ⟶ (Functor.const _).obj (CoefficientSystem.Constructions.Foundations.coefficientBase R K s) where
  app i := ((expansionOverDiagram R K s X).obj i).hom ≫ X.hom
  naturality i j f := by
    change ((expansionOverDiagram R K s X).map f).left ≫
        ((expansionOverDiagram R K s X).obj j).hom ≫ X.hom =
      (((expansionOverDiagram R K s X).obj i).hom ≫ X.hom) ≫ 𝟙 _
    rw [← Category.assoc, Over.w, Category.comp_id]

/-- A morphism from the generic fiber into a finitely presented target extends
after enlarging the finite coefficient base. -/
theorem generic_morphism_descends
    [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [LocallyOfFinitePresentation Y.hom]
    (a : (expansionCone R K s X).pt ⟶ Y.left)
    (ha : a ≫ Y.hom = (expansionOverCone R K s X).pt.hom ≫ X.hom) :
    ∃ (i : Over (op s)) (g : (expansionDiagram R K s X).obj i ⟶ Y.left),
      (expansionCone R K s X).π.app i ≫ g = a ∧
      g ≫ Y.hom = (expansionToBase R K s X).app i := by
  classical
  let : ∀ i, CompactSpace ((expansionDiagram R K s X).obj i) :=
    expansion_compact R K s X
  let : ∀ i, QuasiSeparatedSpace ((expansionDiagram R K s X).obj i) :=
    expansion_quasiSeparated R K s X
  let : ∀ {i j : Over (op s)} (f : i ⟶ j),
      IsAffineHom ((expansionDiagram R K s X).map f) :=
    fun {_ _} f ↦ expansion_transition_affine R K s X f
  apply Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (expansionDiagram R K s X) (expansionToBase R K s X) Y.hom
    (expansionCone R K s X) (expansionConeIsLimit R K s X) a
  ext i
  change ((expansionOverCone R K s X).π.app i).left ≫
      ((expansionOverDiagram R K s X).obj i).hom ≫ X.hom = a ≫ Y.hom
  rw [← Category.assoc, Over.w, ha]
  rfl

/-- Equality on the generic fiber is witnessed after a further enlargement. -/
theorem generic_equation_descends
    [QuasiCompact X.hom]
    (Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [LocallyOfFiniteType Y.hom]
    {i : Over (op s)} (a b : (expansionDiagram R K s X).obj i ⟶ Y.left)
    (ha : (expansionToBase R K s X).app i = a ≫ Y.hom)
    (hb : (expansionToBase R K s X).app i = b ≫ Y.hom)
    (hab : (expansionCone R K s X).π.app i ≫ a =
      (expansionCone R K s X).π.app i ≫ b) :
    ∃ (j : Over (op s)) (hji : j ⟶ i),
      (expansionDiagram R K s X).map hji ≫ a =
        (expansionDiagram R K s X).map hji ≫ b := by
  classical
  let : ∀ i, CompactSpace ((expansionDiagram R K s X).obj i) :=
    expansion_compact R K s X
  let : ∀ {i j : Over (op s)} (f : i ⟶ j),
      IsAffineHom ((expansionDiagram R K s X).map f) :=
    fun {_ _} f ↦ expansion_transition_affine R K s X f
  exact Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (expansionDiagram R K s X) (expansionToBase R K s X) Y.hom
    (expansionCone R K s X) (expansionConeIsLimit R K s X) a b ha hb hab

/-- A quasi-compact open subset of the generic fiber descends to an open
subset of a finite coefficient model. -/
theorem compact_open_descends
    (U : (expansionCone R K s X).pt.Opens)
    (hU : IsCompact (U : Set (expansionCone R K s X).pt)) :
    ∃ (i : Over (op s)) (V : ((expansionDiagram R K s X).obj i).Opens),
      IsCompact (V : Set ((expansionDiagram R K s X).obj i)) ∧
      (expansionCone R K s X).π.app i ⁻¹ᵁ V = U := by
  classical
  let : ∀ {i j : Over (op s)} (f : i ⟶ j),
      IsAffineHom ((expansionDiagram R K s X).map f) :=
    fun {_ _} f ↦ expansion_transition_affine R K s X f
  exact exists_preimage_eq (expansionDiagram R K s X) (expansionCone R K s X)
    (expansionConeIsLimit R K s X) U hU

end OAI.ArithmeticGeometry.Models.Descent.Constructions.Foundations
