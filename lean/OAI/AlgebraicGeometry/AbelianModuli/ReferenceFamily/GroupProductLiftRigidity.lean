import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftOpenCoordinates
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

/-! # Group Product Lift Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupProductLiftRigidity

noncomputable section

/-! Maps on a proper-group product with the same reduction and
the same value on its identity section agree, using the actual
affine identity chart and the proved global-functions theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (T : Over (Spec (.of k))) [IsAffine T.left]
    (Z : Over (Spec (.of k))) [GrpObj Z]
    (B : Over (Spec (.of k))) [IsAffine B.left] (i : B ⟶ Z) [IsOpenImmersion i.left]
    (S : Over (Spec (.of k))) (r : S ⟶ T ⊗ A) [Surjective r.left]
    (x : S ⟶ B) (hx : x ≫ i = 1)

include hx in
theorem properGroupProduct_lift_ext (f g : T ⊗ A ⟶ Z) (hfg : r ≫ f = r ≫ g)
    (he : lift (𝟙 T) (toUnit T ≫ η[A]) ≫ f = lift (𝟙 T) (toUnit T ≫ η[A]) ≫ g) : f = g := by
  let d := (GroupLiftOpenCoordinates.groupLiftOpenEquiv r i x hx g ⟨f, hfg⟩).val
  have hd : d ≫ i = f / g := GroupLiftOpenCoordinates.groupLiftOpenEquiv_fac r i x hx g ⟨f, hfg⟩
  have hc := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroupProduct_affine_target A T B d
  have hconst : f / g = fst T A ≫ lift (𝟙 T) (toUnit T ≫ η[A]) ≫ (f / g) := by
    calc
      f / g = d ≫ i := hd.symm
      _ = (fst T A ≫ lift (𝟙 T) (toUnit T ≫ η[A]) ≫ d) ≫ i := congrArg (fun q => q ≫ i) hc
      _ = fst T A ≫ lift (𝟙 T) (toUnit T ≫ η[A]) ≫ (f / g) := by
        rw [Category.assoc, Category.assoc, hd]
  have hz : f / g = 1 := by
    rw [hconst, GrpObj.comp_div, he, div_self', MonObj.comp_one]
  exact div_eq_one.mp hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupProductLiftRigidity
