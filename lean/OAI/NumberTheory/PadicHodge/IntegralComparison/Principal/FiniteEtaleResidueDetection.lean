import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormInsertion
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdditiveResidue

/-! # Finite Etale Residue Detection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection

noncomputable section

/-! Trace detection on the actual principal finite-etale form diagram.
The original scalar residue is retained as a whole, including its
coefficient and the total-complex signs. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
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
  (U : Z.Opens) (hU : IsAffineOpen U)
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i ⁻¹ᵁ U))
  (g : ℕ)
private abbrev ambientRing : Type u := Γ(Z, U)
private abbrev finiteRing : Type u := IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U
private abbrev scalarImage : Z.Modules :=
  (Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.left.ringCatSheaf)
private abbrev sourceImage : Z.Modules := (Scheme.Modules.pushforward i).obj
  (FiniteEtale.FormSheafDuality.source R Y X f g)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection.ambientRing U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection.finiteRing (f := f) (i := i) (U := U)
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality.source R Y X f g
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection.scalarImage (X := X) (i := i)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection.sourceImage (R := R) (X := X) (Y := Y) (f := f) (i := i) (g := g)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars.modules i U hU N
local instance targetBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i ⁻¹ᵁ U)
local instance sourceBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
local instance baseTower : IsScalarTower R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AffineOpen.DeRhamTrace.sectionTower R Y X f (i ⁻¹ᵁ U)

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U) (c q : ℕ)

def ambientFunctor : ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} A) (.up ℕ) c ⋙
    Supported.CechHomotopyEquivalence.functor W q

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection.ambientFunctor U W c q
local notation "FQ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars.functor i U W c q
local notation "FG" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars.additive i U W c q

variable [Algebra (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) R]
  (ε : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U →ₐ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U] R) (lift : R → ambientRing U)
  (hlift : ∀ r, algebraMap (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) R (i.app U (lift r)) = r)
  (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) g)
  (r : (ambientFunctor U W c q).obj
    (SectionPresheaf.modules U hU (scalarImage (X := X) (i := i))))
  (a : (ambientFunctor U W c q).obj
    (SectionPresheaf.modules U hU (sourceImage (R := R) (X := X) (Y := Y) (f := f) (i := i) (g := g))))
  (hscalar : ∀ s : ambientRing U, algebraMap (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) R (i.app U s) = 0 → s • r = 0)
  (hpair : ∀ x : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U,
    (ambientFunctor U W c q).map ((ModuleFunctor.functor U hU).map
        (FiniteEtaleFormTensor.coefficientIso R X Y f i g).hom ≫
      HomEvaluation.map U hU
        ((Scheme.Modules.pushforward i).obj (FiniteEtale.FormSheafDuality.coefficients R Y X f))
        ((Scheme.Modules.pushforward i).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)) x) a =
      lift (ε x) • (ambientFunctor U W c q).map (PushforwardSection.map i U hU
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
        (Integral.FormSectionUnit.unit R X g (i ⁻¹ᵁ U) ω)) r)

include hlift hscalar hpair in
theorem eq_residue (z : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U)
    (hz :
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
      AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
    (1 ⊗ₜ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U] z : R ⊗[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U] IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) =
      FiniteEtale.FiberSectionTrace.component (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) R ε) :
    a = (F).map (PushforwardSection.map i U hU S
      (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
        (z • OrdinaryFormScalars.Ordinary.map R Q B g ω))) r := by
  let : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  let : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  let e := FiniteEtaleFormTensor.iso R X Y f i U hU hgood g
  let d := ClosedScalars.restrictionIso i U hU N
  let mN := PushforwardSection.map i U hU N
    (Integral.FormSectionUnit.unit R X g (i ⁻¹ᵁ U) ω)
  let y : (FQ).obj P := (F).map d.inv ((F).map mN r)
  let aT : (FQ).obj (FiniteEtale.PresheafTrace.tensor Q B P) := (F).map e.hom a
  have hyD : (F).map d.hom y = (F).map mN r :=
    ConcreteCategory.congr_hom ((F).mapIso d).inv_hom_id ((F).map mN r)
  have hy (s : Q) (hs : algebraMap Q R s = 0) :
      (FG).map (FiniteEtale.PresheafTrace.scalar Q P s) y = 0 := by
    obtain ⟨s₀, hs₀⟩ := i.app_surjective U hU s
    change (FQ).map (FiniteEtale.PresheafTrace.scalar Q P s) y = 0
    rw [← hs₀, ClosedSupportedScalars.scalar_map]
    have hk : algebraMap Q R (i.app U s₀) = 0 := by simpa only [hs₀] using hs
    calc
      s₀ • y = (F).map d.inv ((F).map mN (s₀ • r)) := by simp only [y, map_smul]
      _ = 0 := by rw [hscalar s₀ hk, map_zero, map_zero]
  have ha (x : B) :
      (FG).map (FiniteEtale.PresheafTrace.pairing Q B P x) aT =
        (FG).map (FiniteEtale.PresheafTrace.scalar Q P (i.app U (lift (ε x)))) y := by
    change (FQ).map (FiniteEtale.PresheafTrace.pairing Q B P x) aT =
      (FQ).map (FiniteEtale.PresheafTrace.scalar Q P (i.app U (lift (ε x)))) y
    rw [ClosedSupportedScalars.scalar_map]
    apply (ConcreteCategory.bijective_of_isIso ((F).map d.hom)).injective
    have hp : (F).map d.hom ((FQ).map (FiniteEtale.PresheafTrace.pairing Q B P x) aT) =
        (F).map ((ModuleFunctor.functor U hU).map
            (FiniteEtaleFormTensor.coefficientIso R X Y f i g).hom ≫
          HomEvaluation.map U hU
            ((Scheme.Modules.pushforward i).obj (FiniteEtale.FormSheafDuality.coefficients R Y X f))
            ((Scheme.Modules.pushforward i).obj N) x) a := by
      change (F).map d.hom
        ((F).map ((FiniteEtaleTraceCoordinates.forget i U).map
          (FiniteEtale.PresheafTrace.pairing Q B P x)) ((F).map e.hom a)) = _
      have hp₀ := ConcreteCategory.congr_hom (congrArg (F).map
        (FiniteEtaleFormTensor.pairing R X Y f i U hU hgood g x)) a
      simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hp₀ ⊢
      convert hp₀ using 1
    calc
      _ = _ := hp
      _ = lift (ε x) • (F).map mN r := hpair x
      _ = (F).map d.hom (lift (ε x) • y) := by rw [map_smul, hyD]
  have he := FiniteEtale.AdditiveResidue.eq_inserted Q B R P (FG) ε
    (fun x => i.app U (lift x)) hlift y hy z hz aT ha
  apply (ConcreteCategory.bijective_of_isIso ((F).map e.hom)).injective
  let mS := PushforwardSection.map i U hU S
    (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
      (z • OrdinaryFormScalars.Ordinary.map R Q B g ω))
  calc
    (F).map e.hom a = (FG).map (FiniteEtale.PresheafTrace.insertion Q B P z) y := he
    _ = (F).map (mN ≫ d.inv ≫ (FiniteEtaleTraceCoordinates.forget i U).map
        (FiniteEtale.PresheafTrace.insertion Q B P z)) r := by
      simp only [Functor.map_comp, ConcreteCategory.comp_apply, y]
      rfl
    _ = (F).map (mS ≫ e.hom) r := by
      rw [FiniteEtaleFormInsertion.comparison R X Y f i U hU hgood g z ω]
      rfl
    _ = (F).map e.hom ((F).map mS r) := by
      rw [Functor.map_comp]
      rfl

include hlift hscalar hpair in
theorem exists_residue :
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
      AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
    ∃ z : B,
    (1 ⊗ₜ[Q] z : R ⊗[Q] B) = FiniteEtale.FiberSectionTrace.component Q B R ε ∧
    ε z = 1 ∧
    a = (F).map (PushforwardSection.map i U hU S
      (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
        (z • OrdinaryFormScalars.Ordinary.map R Q B g ω))) r := by
  let : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  let : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  have hQ : Function.Surjective (algebraMap Q R) :=
    fun x => ⟨i.app U (lift x), hlift x⟩
  obtain ⟨z, hz, hε, _⟩ := FiniteEtale.FiberSectionTrace.exists_lift Q B R ε hQ
  exact ⟨z, hz, hε, eq_residue R X Y f i U hU hgood g W c q ε lift hlift ω r a hscalar hpair z hz⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection
