import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormTensor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationAtOne
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormCoherence

/-! # Finite Etale Form Insertion -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormInsertion

noncomputable section

/-! The complete principal diagram of the actual source differential
symbol is tensor insertion of its coefficient into the corresponding
target symbol. Equality at the unit open extends by quasicoherence. -/
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
  (U : Z.Opens) (hU : IsAffineOpen U)
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i ⁻¹ᵁ U))
  (g : ℕ)
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U
private abbrev finiteRing : Type u := IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U
private abbrev scalarImage : Z.Modules :=
  (Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.left.ringCatSheaf)
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormInsertion.finiteRing (f := f) (i := i) (U := U)
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality.source R Y X f g
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormInsertion.scalarImage (X := X) (i := i)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars.modules i U hU N
local notation "r₁" => op (OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne.object U)
local instance targetBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i ⁻¹ᵁ U)
local instance sourceBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
local instance baseTower : IsScalarTower R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
  AffineOpen.DeRhamTrace.sectionTower R Y X f (i ⁻¹ᵁ U)

theorem comparison (b : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) g) :
    PushforwardSection.map i U hU S
        (Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
          (b • OrdinaryFormScalars.Ordinary.map R Q B g ω)) ≫
      (FiniteEtaleFormTensor.iso R X Y f i U hU hgood g).hom =
    PushforwardSection.map i U hU N
        (Integral.FormSectionUnit.unit R X g (i ⁻¹ᵁ U) ω) ≫
      (ClosedScalars.restrictionIso i U hU N).inv ≫
      (FiniteEtaleTraceCoordinates.forget i U).map
        (FiniteEtale.PresheafTrace.insertion Q B P b) := by
  let : Smooth Y.hom := by rw [← Over.w f]; infer_instance
  let : IsProper Y.hom := by rw [← Over.w f]; infer_instance
  let : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := hgood.2.2
  let : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) := f.left.finite_app _ hgood.1
  let : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i U) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i ⁻¹ᵁ U) hgood.1
  let e := FiniteEtaleFormTensor.iso R X Y f i U hU hgood g
  let ωS := Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))
    (b • OrdinaryFormScalars.Ordinary.map R Q B g ω)
  let ωN := Integral.FormSectionUnit.unit R X g (i ⁻¹ᵁ U) ω
  let α := PushforwardSection.map i U hU S ωS ≫ e.hom
  let β := PushforwardSection.map i U hU N ωN ≫
    (ClosedScalars.restrictionIso i U hU N).inv ≫
    (FiniteEtaleTraceCoordinates.forget i U).map
      (FiniteEtale.PresheafTrace.insertion Q B P b)
  have hα : α.app r₁ (AtOne.equiv U M (1 : Q)) =
      b ⊗ₜ[Q] ClosedAtOne.equiv i U N ωN := by
    change e.hom.app r₁
      ((PushforwardSection.map i U hU S ωS).app r₁
        (AtOne.equiv U M (1 : Q))) = _
    rw [PushforwardSection.atOne, one_smul]
    exact FiniteEtaleFormTensor.unit R X Y f i U hU hgood g b ω
  have hβ : β.app r₁ (AtOne.equiv U M (1 : Q)) =
      b ⊗ₜ[Q] ClosedAtOne.equiv i U N ωN := by
    change b ⊗ₜ[Q]
      (show (P).obj r₁ from
        (ClosedScalars.restrictionIso i U hU N).inv.app r₁
          ((PushforwardSection.map i U hU N ωN).app r₁
            (AtOne.equiv U M (1 : Q)))) = _
    rw [PushforwardSection.atOne, one_smul]
    rfl
  have hone := hα.trans hβ.symm
  have hcomponent : α.app r₁ = β.app r₁ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (AtOne.equiv U M).surjective x
    obtain ⟨a, rfl⟩ := i.app_surjective U hU y
    have hm : (i.app U a : Γ(M, U)) = a • (show Γ(M, U) from (1 : Q)) := by
      change i.app U a = i.app U a * 1
      exact (mul_one _).symm
    rw [hm, map_smul, map_smul, map_smul, hone]
    rfl
  let : (SheafOfModules.unit X.left.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  let : (M).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
  let := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g
  let : (S).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left
  let : ((Scheme.Modules.pushforward i).obj S).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
  change α = β
  apply (cancel_mono e.inv).mp
  change (PushforwardSection.map i U hU S ωS ≫ e.hom) ≫ e.inv = β ≫ e.inv
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply SectionTransformationAtOne.Ext.ext_atOne U hU M ((Scheme.Modules.pushforward i).obj S)
  simpa only [α, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using
    congrArg (fun a => a ≫ e.inv.app r₁) hcomponent

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormInsertion
