import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PointedFamilyRigidity
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity
import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.Rigidity.FieldDescent

noncomputable section

/-! Rigidity for pointed maps from an actual smooth proper connected
commutative group, with integrality of the parameter product derived. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PointedFamilyRigidity

variable {k : Type} [Field k] [IsAlgClosed k]
  (Y X : Over (Spec (.of k))) [GrpObj X] [IsCommMonObj X]
  [LocallyOfFiniteType Y.hom] [IsIntegral Y.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]

theorem abelian_parameter_product_integral : IsIntegral (Y ⊗ X).left := by
  have : IsIntegral X.left := Picard.Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group X
  have : GeometricallyIrreducible X.hom :=
    ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction.integral_geometricallyIrreducible_over_algClosed X.hom
  have : GeometricallyReduced X.hom := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.geometricallyReduced_of_smooth X.hom
  have : GeometricallyIntegral X.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  change IsIntegral (pullback Y.hom X.hom)
  infer_instance

variable (Z : Over (Spec (.of k))) [GrpObj Z]
  [LocallyOfFiniteType Z.hom] [IsSeparated Z.hom]

theorem pointedAbelianFamily_eq_fiber
    (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (f : Y ⊗ X ⟶ Z)
    (hf : lift (𝟙 Y) (toUnit Y ≫ η[X]) ≫ f = 1) :
    ∃ g : X ⟶ Z, IsMonHom g ∧ f = snd Y X ≫ g := by
  let g := lift (toUnit X ≫ y₀) (𝟙 X) ≫ f
  have he : η[X] ≫ lift (toUnit X ≫ y₀) (𝟙 X) =
      y₀ ≫ lift (𝟙 Y) (toUnit Y ≫ η[X]) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hg : η[X] ≫ g = η[Z] := by
    change η[X] ≫ lift (toUnit X ≫ y₀) (𝟙 X) ≫ f = η[Z]
    rw [← Category.assoc, he, Category.assoc, hf, MonObj.comp_one]
    rfl
  have : IsMonHom g := Picard.Homomorphisms.GroupRigidity.Construction.pointed_isMonHom X Z g hg
  have : IsIntegral (Y ⊗ X).left := abelian_parameter_product_integral Y X
  exact ⟨g, inferInstance, AbelianScheme.TateComparison.PointedFamilyRigidity.pointedFamily_eq_constant Y X Z y₀ f g hf rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.Rigidity.FieldDescent
