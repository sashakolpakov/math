import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models
import OAI.ArithmeticGeometry.Models.Descent
import OAI.ArithmeticGeometry.Models.FoundationsPullback

/-! # Open Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient

/-! Generalization of the proved OpenModels construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Models of quasi-compact open subsets of a modeled scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.NumberField

universe u

variable {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K]
variable {X : Over (Spec (CommRingCat.of K))} (M : Models.Coefficients.CoefficientModel R₀ K X)

/-- Identify the generic fiber with the limit of expansions of its model. -/
noncomputable def Models.Coefficients.CoefficientModel.expansionGenericIso :
    X.left ≅ (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R₀ K M.coefficients M.model).pt :=
  M.cartesian.flip.isoPullback

noncomputable def Models.Coefficients.CoefficientModel.expansionStageStructure (i : Over (op M.coefficients)) :
    (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionDiagram R₀ K M.coefficients M.model).obj i ⟶
      ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K i.left.unop :=
  pullback.fst (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (leOfHom i.hom.unop)) M.model.hom

noncomputable def Models.Coefficients.CoefficientModel.expansionStageMap (i : Over (op M.coefficients)) :
    X.left ⟶ (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionDiagram R₀ K M.coefficients M.model).obj i :=
  M.expansionGenericIso.hom ≫
    (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R₀ K M.coefficients M.model).π.app i

theorem Models.Coefficients.CoefficientModel.expansionStageCartesian (i : Over (op M.coefficients)) :
    IsPullback (M.expansionStageMap i) X.hom (M.expansionStageStructure i)
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K i.left.unop) := by
  let D := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientSchemeDiagram R₀ K
  let c := (Over.conePost D (op M.coefficients)).obj (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientSchemeCone R₀ K)
  have h : IsPullback (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R₀ K M.coefficients M.model |>.π.app i)
      (pullback.fst (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K M.coefficients) M.model.hom)
      (M.expansionStageStructure i) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K i.left.unop) :=
    ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback M.model.hom (c.π.app i)
  apply h.of_iso' M.expansionGenericIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact (Category.comp_id _).symm
  · exact M.cartesian.flip.isoPullback_hom_fst.trans (Category.comp_id X.hom).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem Models.Coefficients.CoefficientModel.expansionStageFinitePresentation (i : Over (op M.coefficients)) :
    ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (M.expansionStageStructure i) := by
  let : LocallyOfFinitePresentation M.model.hom := M.finitePresentation.1
  let : QuasiCompact M.model.hom := M.finitePresentation.2.1
  let : QuasiSeparated M.model.hom := M.finitePresentation.2.2
  change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.fst _ M.model.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Each expansion stage is again a concrete coefficient model. -/
noncomputable def Models.Coefficients.CoefficientModel.atExpansion (i : Over (op M.coefficients)) :
    Models.Coefficients.CoefficientModel R₀ K X :=
  Models.Coefficients.CoefficientModel.ofCartesian i.left.unop (Over.mk (M.expansionStageStructure i))
    (M.expansionStageFinitePresentation i) (M.expansionStageMap i) (M.expansionStageCartesian i)

@[simp]
theorem Models.Coefficients.CoefficientModel.atExpansion_specialization (i : Over (op M.coefficients)) :
    (M.atExpansion i).specialization = M.expansionStageMap i :=
  Models.Coefficients.CoefficientModel.ofCartesian_specialization ..

include M in
/-- Every quasi-compact open subset of a modeled scheme has a coefficient model. -/
theorem Models.Coefficients.CoefficientModel.open_subset_has_model
    (U : X.left.Opens) (hU : IsCompact (U : Set X.left)) :
    Nonempty (Models.Coefficients.CoefficientModel R₀ K (Over.mk (U.ι ≫ X.hom))) := by
  let e := M.expansionGenericIso
  have hU' : IsCompact (e.inv ⁻¹ᵁ U : Set (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R₀ K M.coefficients M.model).pt) :=
    e.inv.isCompact_preimage hU
  obtain ⟨i, V, hV, hi⟩ := ArithmeticGeometry.Models.Descent.Constructions.Foundations.compact_open_descends R₀ K M.coefficients M.model
    (e.inv ⁻¹ᵁ U) hU'
  have hpre : M.expansionStageMap i ⁻¹ᵁ V = U := by
    change (e.hom ≫ (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R₀ K M.coefficients M.model).π.app i) ⁻¹ᵁ V = U
    rw [Scheme.Hom.comp_preimage, hi, ← Scheme.Hom.comp_preimage, e.hom_inv_id]
    rfl
  let M' := M.atExpansion i
  let V' : M'.model.left.Opens := V
  have hpre' : M'.specialization ⁻¹ᵁ V' = U := by
    change (M.atExpansion i).specialization ⁻¹ᵁ V = U
    rw [Models.Coefficients.CoefficientModel.atExpansion_specialization]
    exact hpre
  let : CompactSpace V'.toScheme := isCompact_iff_compactSpace.mp hV
  let : LocallyOfFinitePresentation M'.model.hom := M'.finitePresentation.1
  let : QuasiSeparated M'.model.hom := M'.finitePresentation.2.2
  let : QuasiSeparatedSpace M'.model.left := quasiSeparatedSpace_of_quasiSeparated M'.model.hom
  let : QuasiSeparatedSpace V'.toScheme := quasiSeparatedSpace_of_quasiSeparated V'.ι
  have hfp : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (V'.ι ≫ M'.model.hom) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  let f := M'.specialization.resLE V' U hpre'.ge
  have hc : IsPullback f U.ι V'.ι M'.specialization :=
    IsOpenImmersion.isPullback _ _ _ _
      (Scheme.Hom.resLE_comp_ι M'.specialization hpre'.ge).symm (by simpa using hpre')
  exact ⟨Models.Coefficients.CoefficientModel.ofCartesian M'.coefficients (Over.mk (V'.ι ≫ M'.model.hom))
    hfp f (hc.paste_vert M'.cartesian)⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient
