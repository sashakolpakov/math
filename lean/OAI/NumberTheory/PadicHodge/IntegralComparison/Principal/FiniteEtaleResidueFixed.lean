import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ScalarAction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdditiveSelectedClass

/-! # Finite Etale Residue Fixed -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueFixed

noncomputable section

/-! The actual selected finite residue is fixed by its source numerator
on the original nested-pushforward supported total. -/
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
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i ⁻¹ᵁ U)) (g : ℕ)
private abbrev ambientRing : Type u := Γ(Z,U)
private abbrev finiteRing : Type u := IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U
private abbrev scalarImage : Z.Modules :=
  (Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.left.ringCatSheaf)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueFixed.ambientRing U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueFixed.finiteRing (f := f) (i := i) (U := U)
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality.source R Y X f g
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars.modules i U hU N
local instance targetBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i ⁻¹ᵁ U)
local instance sourceBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
local instance baseTower : IsScalarTower R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AffineOpen.DeRhamTrace.sectionTower R Y X f (i ⁻¹ᵁ U)
variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U) (c q : ℕ)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection.ambientFunctor U W c q
local notation "FQ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars.functor i U W c q
local notation "FG" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars.additive i U W c q
variable [Algebra (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) R]
  (ε : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U →ₐ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U] R) (lift : R → ambientRing U)
  (hlift : ∀ r, algebraMap (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) R (i.app U (lift r)) = r)
  (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) g)
  (r : (FiniteEtaleResidueDetection.ambientFunctor U W c q).obj
    (SectionPresheaf.modules U hU (scalarImage (X := X) (i := i))))
  (hscalar : ∀ s : ambientRing U, algebraMap (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) R (i.app U s) = 0 → s • r = 0)

include hlift hscalar in
theorem fixed (z : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U)
    (hz :
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
      AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
    (1 ⊗ₜ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U] z : R ⊗[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U] IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) =
      FiniteEtale.FiberSectionTrace.component (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) R ε)
    (he : ε z = 1) :
    (F).map (PrincipalSource.OpenFixedClass.scalar f.left i U hU
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g) z)
      ((F).map (PushforwardSection.map i U hU T
        (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
          (z • OrdinaryFormScalars.Ordinary.map R Q B g ω))) r) =
    (F).map (PushforwardSection.map i U hU T
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
  have hy (s : Q) (hs : algebraMap Q R s = 0) :
      (FG).map (FiniteEtale.PresheafTrace.scalar Q P s) y = 0 := by
    obtain ⟨s₀, hs₀⟩ := i.app_surjective U hU s
    change (FQ).map (FiniteEtale.PresheafTrace.scalar Q P s) y = 0
    rw [← hs₀, ClosedSupportedScalars.scalar_map]
    have hk : algebraMap Q R (i.app U s₀) = 0 := by simpa only [hs₀] using hs
    calc
      s₀ • y = (F).map d.inv ((F).map mN (s₀ • r)) := by simp only [y, map_smul]
      _ = 0 := by rw [hscalar s₀ hk, map_zero, map_zero]
  let mS (b : B) := PushforwardSection.map i U hU T
    (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
      (b • OrdinaryFormScalars.Ordinary.map R Q B g ω))
  have inserted (b : B) : (F).map e.hom ((F).map (mS b) r) =
      (FG).map (FiniteEtale.PresheafTrace.insertion Q B P b) y := by
    have h := ConcreteCategory.congr_hom (congrArg (F).map
      (FiniteEtaleFormInsertion.comparison R X Y f i U hU hgood g b ω)) r
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h
    convert h using 1; rfl
  have hs : mS z ≫ PrincipalSource.OpenFixedClass.scalar f.left i U hU
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g) z = mS (z*z) := by
    dsimp only [mS]
    rw [PrincipalSource.ScalarAction.symbol]
    have hu := (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))).map_smul z
      (z • OrdinaryFormScalars.Ordinary.map R Q B g ω)
    rw [smul_smul] at hu
    rw [← hu]
  change (F).map _ ((F).map (mS z) r) = (F).map (mS z) r
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hs]
  apply (ConcreteCategory.bijective_of_isIso ((F).map e.hom)).injective
  rw [inserted, inserted]
  exact FiniteEtale.AdditiveSelectedClass.fixed Q B R P (FG) ε
    (fun x => i.app U (lift x)) hlift y hy z hz he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueFixed
