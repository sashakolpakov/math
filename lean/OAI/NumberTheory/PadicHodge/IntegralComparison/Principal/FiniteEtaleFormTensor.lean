import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleTraceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedAtOne
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.InternalHom

/-! # Finite Etale Form Tensor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormTensor

noncomputable section

/-! The tensor coordinates of the actual finite-etale form sheaf send
literal source differential symbols to their original coefficient
and target differential symbol at the unit principal open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
attribute [local instance] IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left] [IsProper X.hom] [Smooth X.hom]
  {Z : Scheme.{u}} (i : X.left ⟶ Z) [IsClosedImmersion i]
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality.coefficients R Y X f
local notation "N" g => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local notation "S" g => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality.source R Y X f g
local instance coefficient_qc : (M).IsQuasicoherent :=
  FiniteEtale.FormSheafDuality.coefficient_qc R Y X f

def coefficientIso (g : ℕ) : (Scheme.Modules.pushforward i).obj (S g) ≅
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule ((Scheme.Modules.pushforward i).obj M)
      ((Scheme.Modules.pushforward i).obj (N g)) :=
  (Scheme.Modules.pushforward i).mapIso (FiniteEtale.FormSheafDuality.iso R Y X f g) ≪≫
    Closed.InternalHom.iso i M (N g)

variable (U : Z.Opens) (hU : IsAffineOpen U)
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i ⁻¹ᵁ U))
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U
private abbrev finiteRing : Type u := IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormTensor.finiteRing (f := f) (i := i) (U := U)
local notation "P" g => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars.modules i U hU (N g)
local notation "r₁" => op (OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne.object U)
local instance targetBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i ⁻¹ᵁ U)
local instance sourceBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
local instance baseTower : IsScalarTower R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AffineOpen.DeRhamTrace.sectionTower R Y X f (i ⁻¹ᵁ U)
private abbrev goodChart : FiniteEtale.TraceBasis.Index R Y X f := ⟨i ⁻¹ᵁ U, hgood⟩
local notation "a₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormTensor.goodChart (f := f) (i := i) (U := U) (hgood := hgood)
local instance coordinate_order : LinearOrder
    (FiniteEtale.TraceBasis.coordinateIndex R Y X f (goodChart R X Y f i U hgood)) :=
  FiniteEtale.TraceBasis.coordinateOrder R Y X f a₀

include hgood in
def iso (g : ℕ) : SectionPresheaf.modules U hU ((Scheme.Modules.pushforward i).obj (S g)) ≅
    FiniteEtale.PresheafTrace.tensor Q B (P g) ⋙ ModuleCat.restrictScalars (i.app U).hom := by
  letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  exact (ModuleFunctor.functor U hU).mapIso (coefficientIso R X Y f i g) ≪≫
    FiniteEtaleTraceCoordinates.iso f.left i U hU (N g)

include hU in
theorem evaluation (g : ℕ)
    (z : Γ((Scheme.Modules.pushforward i).obj
      (FiniteEtale.FormSheafDuality.source R Y X f g), U))
    (x : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen ((Scheme.Modules.pushforward i).obj M)
      ((Scheme.Modules.pushforward i).obj (N g)) U
      ((coefficientIso R X Y f i g).hom.app U z) x =
    Intrinsic.EtaleFormRestriction.localEquiv R Y X f a₀ g z x := by
  let : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  let : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  change ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen _ _ U
    ((Closed.InternalHom.iso i M (N g)).hom.app U
      ((FiniteEtale.FormSheafDuality.iso R Y X f g).hom.app (i ⁻¹ᵁ U) z)) x = _
  rw [Closed.InternalHom.iso_app i M (N g) U hU,
    Closed.InternalHom.evaluation i M (N g) U hU,
    FiniteEtale.FormSheafDuality.iso_app R Y X f a₀ g]
  exact FiniteEtale.FormSheafDuality.sectionEquiv_evaluation R Y X f a₀ g z x

theorem pairing (g : ℕ) (x : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
      AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
    (iso R X Y f i U hU hgood g).hom ≫
      (FiniteEtaleTraceCoordinates.forget i U).map
        (FiniteEtale.PresheafTrace.pairing Q B (P g) x) ≫
      (ClosedScalars.restrictionIso i U hU (N g)).hom =
    (ModuleFunctor.functor U hU).map (coefficientIso R X Y f i g).hom ≫
      HomEvaluation.map U hU ((Scheme.Modules.pushforward i).obj M)
        ((Scheme.Modules.pushforward i).obj (N g)) x := by
  let : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  let : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  simpa only [iso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    congrArg (fun a => (ModuleFunctor.functor U hU).map
      (coefficientIso R X Y f i g).hom ≫ a)
      (FiniteEtaleTraceCoordinates.pairing f.left i U hU (N g) x)

theorem atOne_evaluation (g : ℕ)
    (z : Γ((Scheme.Modules.pushforward i).obj
      (FiniteEtale.FormSheafDuality.source R Y X f g), U))
    (x : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
      AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
    FiniteEtale.LineTrace.equiv Q B ((P g).obj r₁)
      ((iso R X Y f i U hU hgood g).hom.app r₁
        (AtOne.equiv U ((Scheme.Modules.pushforward i).obj (S g)) z)) x =
    ClosedAtOne.equiv i U (N g)
      (Intrinsic.EtaleFormRestriction.localEquiv R Y X f a₀ g z x) := by
  let : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  let : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  have h := ConcreteCategory.congr_hom
    (congrArg (fun a => a.app r₁) (pairing R X Y f i U hU hgood g x))
    (AtOne.equiv U ((Scheme.Modules.pushforward i).obj (S g)) z)
  have hn := (ConcreteCategory.congr_hom
    ((AtOne.iso U hU).hom.naturality (coefficientIso R X Y f i g).hom) z).symm
  change ((ModuleFunctor.functor U hU).map (coefficientIso R X Y f i g).hom).app r₁
      (AtOne.equiv U ((Scheme.Modules.pushforward i).obj (S g)) z) =
    AtOne.equiv U
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule ((Scheme.Modules.pushforward i).obj M)
        ((Scheme.Modules.pushforward i).obj (N g)))
      ((coefficientIso R X Y f i g).hom.app U z) at hn
  change FiniteEtale.LineTrace.equiv Q B ((P g).obj r₁)
      ((iso R X Y f i U hU hgood g).hom.app r₁
        (AtOne.equiv U ((Scheme.Modules.pushforward i).obj (S g)) z)) x =
    (HomEvaluation.map U hU ((Scheme.Modules.pushforward i).obj M)
      ((Scheme.Modules.pushforward i).obj (N g)) x).app r₁
      (((ModuleFunctor.functor U hU).map (coefficientIso R X Y f i g).hom).app r₁
        (AtOne.equiv U ((Scheme.Modules.pushforward i).obj (S g)) z)) at h
  rw [hn, HomEvaluation.atOne, evaluation R X Y f i U hU hgood] at h
  exact h

theorem unit (g : ℕ) (b : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) g) :
    (iso R X Y f i U hU hgood g).hom.app r₁
      (AtOne.equiv U ((Scheme.Modules.pushforward i).obj (S g))
        (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
          (b • OrdinaryFormScalars.Ordinary.map R Q B g ω))) =
    b ⊗ₜ[Q] ClosedAtOne.equiv i U (N g)
      (Integral.FormSectionUnit.unit R X g (i ⁻¹ᵁ U) ω) := by
  let : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  let : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  let : Fact (IsAffineOpen (i ⁻¹ᵁ U)) := ⟨hgood.1⟩
  let : Algebra (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U))
      (AffineOpen.DeRhamTrace.sourceRing R Y X f (i ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionAlgebra R Y X f (i ⁻¹ᵁ U)
  let : IsScalarTower R (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U))
      (AffineOpen.DeRhamTrace.sourceRing R Y X f (i ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionTower R Y X f (i ⁻¹ᵁ U)
  let : Algebra.Etale (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U))
      (AffineOpen.DeRhamTrace.sourceRing R Y X f (i ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  let : Module.Free (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U))
      (AffineOpen.DeRhamTrace.sourceRing R Y X f (i ⁻¹ᵁ U)) := hgood.2.2
  let : Module.Finite (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U))
      (AffineOpen.DeRhamTrace.sourceRing R Y X f (i ⁻¹ᵁ U)) := f.left.finite_app _ hgood.1
  let : Algebra (MvPolynomial (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀) R)
      (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U)) :=
    FiniteEtale.TraceBasis.polynomialAlgebra R Y X f a₀
  let : IsScalarTower R (MvPolynomial (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀) R)
      (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U)) :=
    FiniteEtale.TraceBasis.coordinateTower R Y X f a₀
  let : Algebra.Etale (MvPolynomial (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀) R)
      (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U)) :=
    FiniteEtale.TraceBasis.coordinateEtale R Y X f a₀
  let := AffineOpen.DeRhamTrace.polynomialSource R Y X f (i ⁻¹ᵁ U)
    (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀)
  let := AffineOpen.DeRhamTrace.polynomialTower R Y X f (i ⁻¹ᵁ U)
    (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀)
  let := AffineOpen.DeRhamTrace.polynomialBaseTower R Y X f (i ⁻¹ᵁ U)
    (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀)
  let := AffineOpen.DeRhamTrace.sourceEtale R Y X f (i ⁻¹ᵁ U)
    (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀)
  apply (FiniteEtale.LineTrace.equiv Q B ((P g).obj r₁)).injective
  apply LinearMap.ext
  intro x
  rw [atOne_evaluation]
  change ClosedAtOne.equiv i U (N g)
    (Intrinsic.EtaleFormDuality.equiv R Y X f (i ⁻¹ᵁ U)
      (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀) g
      (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
        (b • OrdinaryFormScalars.Ordinary.map R Q B g ω)) x) = _
  rw [Intrinsic.EtaleFormDuality.equiv_unit]
  erw [IntegralComparison.Etale.FormDualTrace.equiv_smul_map R
    (AffineOpen.DeRhamTrace.targetRing R X (i ⁻¹ᵁ U))
    (AffineOpen.DeRhamTrace.sourceRing R Y X f (i ⁻¹ᵁ U))
    (FiniteEtale.TraceBasis.coordinateIndex R Y X f a₀) g b x ω]
  rw [FiniteEtale.LineTrace.equiv_tmul]
  exact ((ClosedAtOne.equiv i U (N g)).toLinearMap.comp
    (Integral.FormSectionUnit.unit R X g (i ⁻¹ᵁ U))).map_smul
      (Algebra.trace Q B (b*x)) ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormTensor
