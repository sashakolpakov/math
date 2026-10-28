import OAI.ArithmeticGeometry.Models.Descent
import OAI.ArithmeticGeometry.Models.FoundationsPullback

/-! # Open -/

namespace OAI.ArithmeticGeometry.Models

/-! Models of quasi-compact open subsets of a modeled scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.NumberField

universe u

variable {K : Type u} [Field K]
variable {X : Over (Spec (CommRingCat.of K))} (M : Foundations.Constructions.CoefficientModel K X)

/-- Identify the generic fiber with the limit of expansions of its model. -/
noncomputable def Foundations.Constructions.CoefficientModel.expansionGenericIso :
    X.left ≅ (Descent.Constructions.Foundations.expansionCone (𝓞 K) K M.coefficients M.model).pt :=
  M.cartesian.flip.isoPullback

noncomputable def Foundations.Constructions.CoefficientModel.expansionStageStructure (i : Over (op M.coefficients)) :
    (Descent.Constructions.Foundations.expansionDiagram (𝓞 K) K M.coefficients M.model).obj i ⟶
      CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K i.left.unop :=
  pullback.fst (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (leOfHom i.hom.unop)) M.model.hom

noncomputable def Foundations.Constructions.CoefficientModel.expansionStageMap (i : Over (op M.coefficients)) :
    X.left ⟶ (Descent.Constructions.Foundations.expansionDiagram (𝓞 K) K M.coefficients M.model).obj i :=
  M.expansionGenericIso.hom ≫
    (Descent.Constructions.Foundations.expansionCone (𝓞 K) K M.coefficients M.model).π.app i

theorem Foundations.Constructions.CoefficientModel.expansionStageCartesian (i : Over (op M.coefficients)) :
    IsPullback (M.expansionStageMap i) X.hom (M.expansionStageStructure i)
      (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K i.left.unop) := by
  let D := CoefficientSystem.Constructions.Foundations.coefficientSchemeDiagram (𝓞 K) K
  let c := (Over.conePost D (op M.coefficients)).obj (CoefficientSystem.Constructions.Foundations.coefficientSchemeCone (𝓞 K) K)
  have h : IsPullback (Descent.Constructions.Foundations.expansionCone (𝓞 K) K M.coefficients M.model |>.π.app i)
      (pullback.fst (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M.coefficients) M.model.hom)
      (M.expansionStageStructure i) (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K i.left.unop) :=
    FoundationsPullback.Constructions.pullback_over_map_isPullback M.model.hom (c.π.app i)
  apply h.of_iso' M.expansionGenericIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact (Category.comp_id _).symm
  · exact M.cartesian.flip.isoPullback_hom_fst.trans (Category.comp_id X.hom).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem Foundations.Constructions.CoefficientModel.expansionStageFinitePresentation (i : Over (op M.coefficients)) :
    Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (M.expansionStageStructure i) := by
  let : LocallyOfFinitePresentation M.model.hom := M.finitePresentation.1
  let : QuasiCompact M.model.hom := M.finitePresentation.2.1
  let : QuasiSeparated M.model.hom := M.finitePresentation.2.2
  change Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.fst _ M.model.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Each expansion stage is again a concrete coefficient model. -/
noncomputable def Foundations.Constructions.CoefficientModel.atExpansion (i : Over (op M.coefficients)) :
    Foundations.Constructions.CoefficientModel K X :=
  Foundations.Constructions.CoefficientModel.ofCartesian i.left.unop (Over.mk (M.expansionStageStructure i))
    (M.expansionStageFinitePresentation i) (M.expansionStageMap i) (M.expansionStageCartesian i)

@[simp]
theorem Foundations.Constructions.CoefficientModel.atExpansion_specialization (i : Over (op M.coefficients)) :
    (M.atExpansion i).specialization = M.expansionStageMap i :=
  Foundations.Constructions.CoefficientModel.ofCartesian_specialization ..

include M in
/-- Every quasi-compact open subset of a modeled scheme has a coefficient model. -/
theorem Foundations.Constructions.CoefficientModel.open_subset_has_model
    (U : X.left.Opens) (hU : IsCompact (U : Set X.left)) :
    Nonempty (Foundations.Constructions.CoefficientModel K (Over.mk (U.ι ≫ X.hom))) := by
  let e := M.expansionGenericIso
  have hU' : IsCompact (e.inv ⁻¹ᵁ U : Set (Descent.Constructions.Foundations.expansionCone (𝓞 K) K M.coefficients M.model).pt) :=
    e.inv.isCompact_preimage hU
  obtain ⟨i, V, hV, hi⟩ := Descent.Constructions.Foundations.compact_open_descends (𝓞 K) K M.coefficients M.model
    (e.inv ⁻¹ᵁ U) hU'
  have hpre : M.expansionStageMap i ⁻¹ᵁ V = U := by
    change (e.hom ≫ (Descent.Constructions.Foundations.expansionCone (𝓞 K) K M.coefficients M.model).π.app i) ⁻¹ᵁ V = U
    rw [Scheme.Hom.comp_preimage, hi, ← Scheme.Hom.comp_preimage, e.hom_inv_id]
    rfl
  let M' := M.atExpansion i
  let V' : M'.model.left.Opens := V
  have hpre' : M'.specialization ⁻¹ᵁ V' = U := by
    change (M.atExpansion i).specialization ⁻¹ᵁ V = U
    rw [Foundations.Constructions.CoefficientModel.atExpansion_specialization]
    exact hpre
  let : CompactSpace V'.toScheme := isCompact_iff_compactSpace.mp hV
  let : LocallyOfFinitePresentation M'.model.hom := M'.finitePresentation.1
  let : QuasiSeparated M'.model.hom := M'.finitePresentation.2.2
  let : QuasiSeparatedSpace M'.model.left := quasiSeparatedSpace_of_quasiSeparated M'.model.hom
  let : QuasiSeparatedSpace V'.toScheme := quasiSeparatedSpace_of_quasiSeparated V'.ι
  have hfp : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (V'.ι ≫ M'.model.hom) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  let f := M'.specialization.resLE V' U hpre'.ge
  have hc : IsPullback f U.ι V'.ι M'.specialization :=
    IsOpenImmersion.isPullback _ _ _ _
      (Scheme.Hom.resLE_comp_ι M'.specialization hpre'.ge).symm (by simpa using hpre')
  exact ⟨Foundations.Constructions.CoefficientModel.ofCartesian M'.coefficients (Over.mk (V'.ι ≫ M'.model.hom))
    hfp f (hc.paste_vert M'.cartesian)⟩

end OAI.ArithmeticGeometry.Models
