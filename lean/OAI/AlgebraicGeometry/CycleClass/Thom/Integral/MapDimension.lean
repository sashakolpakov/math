import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineGenericRank
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Map Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension.Constructions

noncomputable section

/-! Integral dominant maps preserve the actual function-field dimension.
In particular every reduced support under a finite map retains its dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineGenericRank.Constructions.Construction

variable {S T : Scheme} [IsIntegral S] [IsIntegral T]

theorem dominant_app_injective (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T)
    (U : T.Opens) (hU : genericPoint T ∈ U) : Function.Injective (i.app U) := by
  have hV : genericPoint S ∈ i ⁻¹ᵁ U := by
    change i (genericPoint S) ∈ U
    rw [hη]
    exact hU
  have hc := ProperImage.AffineGenericRank.Constructions.Construction.genericFieldMap_germ_appLE i hη U (i ⁻¹ᵁ U) le_rfl hU hV
  rw [← Scheme.Hom.app_eq_appLE] at hc
  intro a b hab
  apply germ_injective_of_isIntegral T (genericPoint T) hU
  apply (ProperImage.FunctionFields.Constructions.Construction.genericFieldMap i hη).hom.injective
  exact (ConcreteCategory.congr_hom hc a).trans
    ((congrArg (S.presheaf.germ (i ⁻¹ᵁ U) (genericPoint S) hV) hab).trans
      (ConcreteCategory.congr_hom hc b).symm)

/-- The affine integral extension gives equality of the actual dimensions,
using the original base-field maps on sections and function fields. -/
theorem integral_dominant_dimension (i : S ⟶ T) [IsIntegralHom i]
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g) := by
  obtain ⟨U, hU, hηU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (genericPoint T))
  let : Nonempty U := ⟨⟨genericPoint T, hηU⟩⟩
  let : Nonempty (i ⁻¹ᵁ U) := ⟨⟨genericPoint S, by
    change i (genericPoint S) ∈ U
    rw [hη]
    exact hηU⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (i ≫ g) (i ⁻¹ᵁ U)
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections g U hU,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections (i ≫ g) (i ⁻¹ᵁ U) (hU.preimage i)]
  exact congrArg Cardinal.toNat (Foundations.Scheme.TranscendenceDegreeTransfer.trdeg_eq_of_injective_integral_algHom ℂ
    (Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom i g U) (dominant_app_injective i hη U hηU) (i.isIntegral_app U hU))

/-- A finite map preserves the dimension of each original reduced support. -/
theorem finite_support_dimension {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsFinite f.left]
    (Z : IrreducibleCloseds X.left) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom := by
  let i := Thom.Scheme.ProperSupport.Constructions.imageMap f Z
  let : IsFinite i := Thom.Scheme.ProperSupport.Constructions.imageMap_finite f Z
  have h := integral_dominant_dimension i (Thom.Scheme.ProperSupport.Constructions.imageMap_genericPoint f Z)
    (Geometric.SupportFiniteType.supportStructureMap (Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom)
  rw [Thom.Scheme.ProperSupport.Constructions.imageMap_over] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension.Constructions
