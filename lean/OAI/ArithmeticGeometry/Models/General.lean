import OAI.ArithmeticGeometry.Models.Glued

/-! # General -/

namespace OAI.ArithmeticGeometry.Models.General.Constructions.Foundations

/-! Every scheme of finite presentation over the number field has a coefficient model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.NumberField

universe u

noncomputable def openOver {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) : Over S :=
  Over.mk (U.ι ≫ X.hom)

noncomputable def openOverMap {S : Scheme.{u}} (X : Over S) {U V : X.left.Opens} (h : U ≤ V) :
    openOver X U ⟶ openOver X V :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ (V.ι ≫ X.hom) = U.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem openOverMap_open {S : Scheme.{u}} (X : Over S) {U V : X.left.Opens} (h : U ≤ V) :
    IsOpenImmersion (openOverMap X h).left := by
  change IsOpenImmersion (X.left.homOfLE h)
  infer_instance

theorem openOver_union_pushout {S : Scheme.{u}} (X : Over S) (U V : X.left.Opens) :
    IsPushout (openOverMap X (show U ⊓ V ≤ U from inf_le_left)).left
      (openOverMap X (show U ⊓ V ≤ V from inf_le_right)).left
      (openOverMap X (show U ≤ U ⊔ V from le_sup_left)).left
      (openOverMap X (show V ≤ U ⊔ V from le_sup_right)).left := by
  let i := openOverMap X (show U ≤ U ⊔ V from le_sup_left)
  let j := openOverMap X (show V ≤ U ⊔ V from le_sup_right)
  let : IsOpenImmersion i.left := openOverMap_open X _
  let : IsOpenImmersion j.left := openOverMap_open X _
  apply OpenPushout.Constructions.Foundations.openPair_isPushout _ _ i.left j.left ?_
    (isPullback_opens_inf_le (show U ≤ U ⊔ V from le_sup_left)
      (show V ≤ U ⊔ V from le_sup_right))
  intro x
  rcases x.2 with hU | hV
  · left
    refine ⟨⟨x.1, hU⟩, ?_⟩
    apply Subtype.ext
    exact X.left.homOfLE_apply (show U ≤ U ⊔ V from le_sup_left) ⟨x.1, hU⟩
  · right
    refine ⟨⟨x.1, hV⟩, ?_⟩
    apply Subtype.ext
    exact X.left.homOfLE_apply (show V ≤ U ⊔ V from le_sup_right) ⟨x.1, hV⟩

theorem scheme_has_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K))) (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    Nonempty (Foundations.Constructions.CoefficientModel K X) := by
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : QuasiCompact X.hom := hX.2.1
  let : QuasiSeparated X.hom := hX.2.2
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsNoetherian X.left := ⟨⟩
  have hOpen (U : X.left.Opens) : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (openOver X U).hom := by
    let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
    let : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
    change Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (U.ι ≫ X.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hModels (U : X.left.Opens) : Nonempty (Foundations.Constructions.CoefficientModel K (openOver X U)) := by
    refine compact_open_induction_on
      (P := fun U ↦ Nonempty (Foundations.Constructions.CoefficientModel K (openOver X U))) U
      (NoetherianSpace.isCompact _) ?_ ?_
    · let : IsAffine (openOver X ⊥).left := isAffineOpen_bot X.left
      exact Foundations.Constructions.isAffine_has_coefficient_model (openOver X ⊥) (hOpen ⊥)
    · intro U _hU V ih
      let A := openOver X U
      let B := openOver X V
      let W := openOver X (U ⊓ V)
      let f : W ⟶ A := openOverMap X inf_le_left
      let g : W ⟶ B := openOverMap X inf_le_right
      let : IsOpenImmersion f.left := openOverMap_open X _
      let : IsOpenImmersion g.left := openOverMap_open X _
      let : CompactSpace W.left := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
      let : IsAffine B.left := V.2
      obtain ⟨MA⟩ := ih
      obtain ⟨MB⟩ := Foundations.Constructions.isAffine_has_coefficient_model B (hOpen V)
      exact Glued.Constructions.Foundations.open_gluing_has_model f g (openOverMap X le_sup_left) (openOverMap X le_sup_right)
        (openOver_union_pushout X U V) MA MB
  obtain ⟨M⟩ := hModels ⊤
  let e : openOver X ⊤ ≅ X := Over.isoMk X.left.topIso (by rfl)
  exact ⟨M.transport e⟩

end OAI.ArithmeticGeometry.Models.General.Constructions.Foundations
