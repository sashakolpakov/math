import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar
import OAI.AlgebraicGeometry.Betti.AffineDimension
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed Immersion Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension

noncomputable section

/-!
# Dimension monotonicity for closed immersions

The algebraic comparison uses a surjection between affine coordinate rings.
It does not assert a map between the two function fields: a closed immersion
does not in general induce such a map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

/-- Quotienting an integral algebra cannot increase the transcendence degree
of its fraction field. -/
theorem fractionRing_trdeg_le_of_surjective_algHom
    (k : Type u) {A B : Type v} [Field k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    Algebra.trdeg k (FractionRing B) ≤ Algebra.trdeg k (FractionRing A) := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k B, ← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k A]
  exact trdeg_le_of_surjective f hf

/-- The same comparison for any actual fraction fields, with their compatible
base-field scalar structures. -/
theorem fractionField_trdeg_le_of_surjective_algHom
    (k : Type u) {A B KA KB : Type v} [Field k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Field KA] [Field KB]
    [Algebra k A] [Algebra k B] [Algebra k KA] [Algebra k KB]
    [Algebra A KA] [Algebra B KB] [IsScalarTower k A KA] [IsScalarTower k B KB]
    [IsFractionRing A KA] [IsFractionRing B KB]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    Algebra.trdeg k KB ≤ Algebra.trdeg k KA := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_of_isFractionRing k B KB, ← TranscendenceDegreeTransfer.trdeg_eq_of_isFractionRing k A KA]
  exact trdeg_le_of_surjective f hf

/-- The fraction-ring inequality with explicit cardinal lifts when the two
coordinate rings live in different universes. -/
theorem lift_fractionRing_trdeg_le_of_surjective_algHom
    (k : Type u) {A : Type v} {B : Type w} [Field k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    Cardinal.lift.{v} (Algebra.trdeg k (FractionRing B)) ≤
      Cardinal.lift.{w} (Algebra.trdeg k (FractionRing A)) := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k B, ← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k A]
  exact lift_trdeg_le_of_surjective f hf

/-- Restriction along a scheme morphism commutes with the actual base-section
map on an open set and its inverse image. -/
theorem sectionBaseMap_app {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S)
    (U : X.Opens) :
    Betti.AffineDimension.Realization.sectionBaseMap f U ≫ i.app U =
      Betti.AffineDimension.Realization.sectionBaseMap (i ≫ f) (i ⁻¹ᵁ U) := by
  dsimp only [Betti.AffineDimension.Realization.sectionBaseMap]
  rw [i.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE i f ⊤ U (i ⁻¹ᵁ U) le_top le_rfl

/-- Pullback on sections respects the scalar map induced by the structure
morphism to the spectrum of the scalar ring. -/
theorem specSectionScalarMap_app {k : Type u} [CommRing k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    (i.app U).hom.comp (SpecScalarTransport.specSectionScalarMap f U) =
      SpecScalarTransport.specSectionScalarMap (i ≫ f) (i ⁻¹ᵁ U) := by
  ext r
  exact congrArg
    (fun q : Γ(Spec (.of k), ⊤) ⟶ Γ(Z, i ⁻¹ᵁ U) =>
      q ((Scheme.ΓSpecIso (.of k)).inv r))
    (sectionBaseMap_app i f U)

/-- The existing section pullback as an algebra homomorphism for the actual
base-ring scalar structures. -/
def sectionPullbackAlgHom {k : Type u} [CommRing k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    letI := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
    Γ(X, U) →ₐ[k] Γ(Z, i ⁻¹ᵁ U) := by
  letI := SpecScalarTransport.specSectionScalarAlgebra f U
  letI := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
  exact
    { (i.app U).hom with
      commutes' := fun r => congrArg (fun h : k →+* Γ(Z, i ⁻¹ᵁ U) => h r)
        (specSectionScalarMap_app i f U) }

/-- On an affine open of the target, a closed immersion gives a surjective
algebra homomorphism of the actual section rings. -/
theorem sectionPullbackAlgHom_surjective {k : Type u} [CommRing k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of k)) (U : X.Opens) (hU : IsAffineOpen U) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    letI := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
    Function.Surjective (sectionPullbackAlgHom i f U) :=
  i.app_surjective U hU

/-- A nonempty common affine chart compares the actual function fields of
an integral closed subscheme and its integral ambient scheme. -/
theorem closedImmersion_functionField_trdeg_le_of_affineOpen
    {k : Type u} [Field k] {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k))
    (U : X.Opens) [hV : Nonempty (i ⁻¹ᵁ U)] (hU : IsAffineOpen U) :
    let := FunctionFieldScalar.functionFieldScalarAlgebra f
    let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    Algebra.trdeg k Z.functionField ≤ Algebra.trdeg k X.functionField := by
  let z := Classical.choice hV
  let : Nonempty U := ⟨⟨i z.val, z.property⟩⟩
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower f U
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower (i ≫ f) (i ⁻¹ᵁ U)
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let := functionField_isFractionRing_of_isAffineOpen Z (i ⁻¹ᵁ U) (hU.preimage i)
  exact fractionField_trdeg_le_of_surjective_algHom k
    (KA := X.functionField) (KB := Z.functionField)
    (sectionPullbackAlgHom i f U) (sectionPullbackAlgHom_surjective i f U hU)

/-- A closed immersion between integral schemes cannot increase the
transcendence degree of the actual function field over the given scalar field.
The proof uses an affine chart around the image of the source generic point. -/
theorem closedImmersion_functionField_trdeg_le
    {k : Type u} [Field k] {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) :
    let := FunctionFieldScalar.functionFieldScalarAlgebra f
    let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    Algebra.trdeg k Z.functionField ≤ Algebra.trdeg k X.functionField := by
  let z := genericPoint Z
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx (i z))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let : Nonempty (i ⁻¹ᵁ U) := ⟨⟨z, X.affineCover.covers (i z)⟩⟩
  exact closedImmersion_functionField_trdeg_le_of_affineOpen i f U hU

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension
