import OAI.ArithmeticGeometry.Models.CoefficientSystem
import OAI.ArithmeticGeometry.Models.Scheme
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Foundations -/

namespace OAI.ArithmeticGeometry.Models.Foundations.Constructions

/-! Concrete finite coefficient models and enlargement of their base rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField TensorProduct

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A model consists of a scheme over a finite coefficient ring and an actual
isomorphism identifying its generic base change with the given scheme. -/
structure CoefficientModel (X : Over (Spec (CommRingCat.of K))) where
  coefficients : Finset K
  model : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K coefficients)
  finitePresentation : Scheme.Constructions.Foundations.FinitePresentationMorphism model.hom
  genericIso : (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K coefficients)).obj model ≅ X

variable {K}

/-- The map from the generic fiber to its coefficient model. -/
noncomputable def CoefficientModel.specialization
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel K X) :
    X.left ⟶ M.model.left :=
  M.genericIso.inv.left ≫ pullback.fst M.model.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M.coefficients)

omit [NumberField K] in
theorem CoefficientModel.cartesian
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel K X) :
    IsPullback M.specialization X.hom M.model.hom
      (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M.coefficients) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    ((Over.forget (Spec (CommRingCat.of K))).mapIso M.genericIso.symm) rfl ?_
  · dsimp [CoefficientModel.specialization]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M.coefficients) M.genericIso.inv.w
  · exact M.genericIso.inv.w

/-- Construct the generic-fiber isomorphism from a cartesian square. -/
noncomputable def CoefficientModel.ofCartesian
    {X : Over (Spec (CommRingCat.of K))} (s : Finset K)
    (Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (hY : Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (f : X.left ⟶ Y.left) (h : IsPullback f X.hom Y.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) :
    CoefficientModel K X where
  coefficients := s
  model := Y
  finitePresentation := hY
  genericIso := Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

omit [NumberField K] in
@[simp]
theorem CoefficientModel.ofCartesian_specialization
    {X : Over (Spec (CommRingCat.of K))} (s : Finset K)
    (Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (hY : Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (f : X.left ⟶ Y.left) (h : IsPullback f X.hom Y.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) :
    (CoefficientModel.ofCartesian s Y hY f h).specialization = f :=
  h.isoPullback_hom_fst

/-- Transport a constructed model along an isomorphism of generic fibers. -/
noncomputable def CoefficientModel.transport
    {X Y : Over (Spec (CommRingCat.of K))} (M : CoefficientModel K X) (e : X ≅ Y) :
    CoefficientModel K Y :=
  { M with genericIso := M.genericIso ≪≫ e }

/-- Pulling a model back to a larger finite coefficient ring preserves its generic fiber. -/
noncomputable def CoefficientModel.enlarge
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel K X)
    (s : Finset K) (h : M.coefficients ⊆ s) : CoefficientModel K X := by
  let f := CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h
  let Y := (Over.pullback f).obj M.model
  have hY : Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom := by
    let : LocallyOfFinitePresentation M.model.hom := M.finitePresentation.1
    let : QuasiCompact M.model.hom := M.finitePresentation.2.1
    let : QuasiSeparated M.model.hom := M.finitePresentation.2.2
    change Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.snd M.model.hom _)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let g : X.left ⟶ Y.left := pullback.lift M.specialization
    (X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) (by
      rw [M.cartesian.w, Category.assoc, CoefficientSystem.Constructions.Foundations.genericBaseMap_comp])
  have hg : IsPullback g X.hom Y.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) := by
    apply IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback M.model.hom f)
    rw [pullback.lift_fst, CoefficientSystem.Constructions.Foundations.genericBaseMap_comp]
    exact M.cartesian
  exact CoefficientModel.ofCartesian s Y hY g hg

omit [NumberField K] in
@[reassoc (attr := simp)]
theorem CoefficientModel.enlarge_specialization_fst
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel K X)
    (s : Finset K) (h : M.coefficients ⊆ s) :
    (M.enlarge s h).specialization ≫ pullback.fst M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) =
      M.specialization := by
  simp only [CoefficientModel.enlarge, CoefficientModel.ofCartesian_specialization]
  exact pullback.lift_fst _ _ _

omit [NumberField K] in
@[reassoc (attr := simp)]
theorem CoefficientModel.enlarge_specialization_snd
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel K X)
    (s : Finset K) (h : M.coefficients ⊆ s) :
    (M.enlarge s h).specialization ≫ pullback.snd M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) =
      X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s := by
  simp only [CoefficientModel.enlarge, CoefficientModel.ofCartesian_specialization]
  exact pullback.lift_snd _ _ _

omit [NumberField K] in
/-- A finite algebra presentation produces a model over its finite set of coefficients. -/
theorem affine_has_coefficient_model
    (A : Type u) [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] :
    Nonempty (CoefficientModel K (Scheme.Constructions.Foundations.affineOver K A)) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation K A
  let s : Finset K := P.finite_coeffs.toFinset
  let L := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s
  let : P.HasCoeffs L := ⟨fun c hc ↦ ⟨⟨c, Algebra.subset_adjoin (by simpa [s] using hc)⟩, rfl⟩⟩
  let A₀ := P.ModelOfHasCoeffs L
  exact ⟨{
    coefficients := s
    model := Scheme.Constructions.Foundations.affineOver L A₀
    finitePresentation := Scheme.Constructions.Foundations.affineOver_finitePresentation L A₀
    genericIso := Scheme.Constructions.Foundations.baseChangeAffineIso L K A₀ ≪≫
      Scheme.Constructions.Foundations.affineOverIso (P.tensorModelOfHasCoeffsEquiv L)
  }⟩

omit [NumberField K] in
/-- The affine model construction applies to arbitrary affine objects in the over category. -/
theorem isAffine_has_coefficient_model
    (X : Over (Spec (CommRingCat.of K))) [IsAffine X.left]
    (hX : Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) : Nonempty (CoefficientModel K X) := by
  let : LocallyOfFinitePresentation X.hom := hX.1
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let A := Γ(X.left, ⊤)
  let : Algebra K A := φ.hom.toAlgebra
  have hφFP : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    infer_instance
  let : Algebra.FinitePresentation K A :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp hφFP
  obtain ⟨M⟩ := affine_has_coefficient_model (K := K) A
  have e : X ≅ Scheme.Constructions.Foundations.affineOver K A := Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.map φ = X.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  exact ⟨M.transport e.symm⟩

end OAI.ArithmeticGeometry.Models.Foundations.Constructions
