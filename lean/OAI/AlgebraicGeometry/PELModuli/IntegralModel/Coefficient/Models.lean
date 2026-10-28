import OAI.ArithmeticGeometry.Models.CoefficientSystem
import OAI.ArithmeticGeometry.Models.Scheme
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients

/-! Finite coefficient models over an arbitrary coefficient ring.
This generalizes the proved constructions in Models from the ring of
integers to R, so they apply to complex schemes over a specified number field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField TensorProduct

universe u

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

/-- A model consists of a scheme over a finite coefficient ring and an actual
isomorphism identifying its generic base change with the given scheme. -/
structure CoefficientModel (X : Over (Spec (CommRingCat.of K))) where
  coefficients : Finset K
  model : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K coefficients)
  finitePresentation : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism model.hom
  genericIso : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K coefficients)).obj model ≅ X

variable {R K}

/-- The map from the generic fiber to its coefficient model. -/
noncomputable def CoefficientModel.specialization
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel R K X) :
    X.left ⟶ M.model.left :=
  M.genericIso.inv.left ≫ pullback.fst M.model.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K M.coefficients)

theorem CoefficientModel.cartesian
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel R K X) :
    IsPullback M.specialization X.hom M.model.hom
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K M.coefficients) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    ((Over.forget (Spec (CommRingCat.of K))).mapIso M.genericIso.symm) rfl ?_
  · dsimp [CoefficientModel.specialization]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K M.coefficients) M.genericIso.inv.w
  · exact M.genericIso.inv.w

/-- Construct the generic-fiber isomorphism from a cartesian square. -/
noncomputable def CoefficientModel.ofCartesian
    {X : Over (Spec (CommRingCat.of K))} (s : Finset K)
    (Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (f : X.left ⟶ Y.left) (h : IsPullback f X.hom Y.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)) :
    CoefficientModel R K X where
  coefficients := s
  model := Y
  finitePresentation := hY
  genericIso := Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

@[simp]
theorem CoefficientModel.ofCartesian_specialization
    {X : Over (Spec (CommRingCat.of K))} (s : Finset K)
    (Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (f : X.left ⟶ Y.left) (h : IsPullback f X.hom Y.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)) :
    (CoefficientModel.ofCartesian s Y hY f h).specialization = f :=
  h.isoPullback_hom_fst

/-- Transport a constructed model along an isomorphism of generic fibers. -/
noncomputable def CoefficientModel.transport
    {X Y : Over (Spec (CommRingCat.of K))} (M : CoefficientModel R K X) (e : X ≅ Y) :
    CoefficientModel R K Y :=
  { M with genericIso := M.genericIso ≪≫ e }

/-- Pulling a model back to a larger finite coefficient ring preserves its generic fiber. -/
noncomputable def CoefficientModel.enlarge
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel R K X)
    (s : Finset K) (h : M.coefficients ⊆ s) : CoefficientModel R K X := by
  let f := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h
  let Y := (Over.pullback f).obj M.model
  have hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom := by
    let : LocallyOfFinitePresentation M.model.hom := M.finitePresentation.1
    let : QuasiCompact M.model.hom := M.finitePresentation.2.1
    let : QuasiSeparated M.model.hom := M.finitePresentation.2.2
    change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.snd M.model.hom _)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let g : X.left ⟶ Y.left := pullback.lift M.specialization
    (X.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) (by
      rw [M.cartesian.w, Category.assoc, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap_comp])
  have hg : IsPullback g X.hom Y.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) := by
    apply IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback M.model.hom f)
    rw [pullback.lift_fst, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap_comp]
    exact M.cartesian
  exact CoefficientModel.ofCartesian s Y hY g hg

@[reassoc (attr := simp)]
theorem CoefficientModel.enlarge_specialization_fst
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel R K X)
    (s : Finset K) (h : M.coefficients ⊆ s) :
    (M.enlarge s h).specialization ≫ pullback.fst M.model.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) =
      M.specialization := by
  simp only [CoefficientModel.enlarge, CoefficientModel.ofCartesian_specialization]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem CoefficientModel.enlarge_specialization_snd
    {X : Over (Spec (CommRingCat.of K))} (M : CoefficientModel R K X)
    (s : Finset K) (h : M.coefficients ⊆ s) :
    (M.enlarge s h).specialization ≫ pullback.snd M.model.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) =
      X.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s := by
  simp only [CoefficientModel.enlarge, CoefficientModel.ofCartesian_specialization]
  exact pullback.lift_snd _ _ _

/-- A finite algebra presentation produces a model over its finite set of coefficients. -/
theorem affine_has_coefficient_model
    (A : Type u) [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] :
    Nonempty (CoefficientModel R K (ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver K A)) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation K A
  let s : Finset K := P.finite_coeffs.toFinset
  let L := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s
  let : P.HasCoeffs L := ⟨fun c hc ↦ ⟨⟨c, Algebra.subset_adjoin (by simpa [s] using hc)⟩, rfl⟩⟩
  let A₀ := P.ModelOfHasCoeffs L
  exact ⟨{
    coefficients := s
    model := ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver L A₀
    finitePresentation := ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver_finitePresentation L A₀
    genericIso := ArithmeticGeometry.Models.Scheme.Constructions.Foundations.baseChangeAffineIso L K A₀ ≪≫
      ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOverIso (P.tensorModelOfHasCoeffsEquiv L)
  }⟩

/-- The affine model construction applies to arbitrary affine objects in the over category. -/
theorem isAffine_has_coefficient_model
    (X : Over (Spec (CommRingCat.of K))) [IsAffine X.left]
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) : Nonempty (CoefficientModel R K X) := by
  let : LocallyOfFinitePresentation X.hom := hX.1
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let A := Γ(X.left, ⊤)
  let : Algebra K A := φ.hom.toAlgebra
  have hφFP : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    infer_instance
  let : Algebra.FinitePresentation K A :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp hφFP
  obtain ⟨M⟩ := affine_has_coefficient_model (R := R) (K := K) A
  have e : X ≅ ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver K A := Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.map φ = X.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  exact ⟨M.transport e.symm⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients
