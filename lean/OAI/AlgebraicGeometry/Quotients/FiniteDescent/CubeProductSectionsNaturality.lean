import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSections

/-! # Cube Product Sections Naturality -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech

noncomputable section

/-! Tensor coordinates for product sections commute with restrictions to smaller rectangles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {U U' : X.Opens} {V V' : Y.Opens} (i : U' ⟶ U) (j : V' ⟶ V)

include i j

theorem productRectangle_mono : CubeProductSections.Construction.CubeCech.productRectangle f g U' V' ≤ CubeProductSections.Construction.CubeCech.productRectangle f g U V :=
  inf_le_inf ((pullback.fst f g).preimage_mono i.le) ((pullback.snd f g).preimage_mono j.le)

theorem productRectangleLeftMap_restrict :
    X.presheaf.map i.op ≫ CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g U' V' =
      CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g U V ≫ (pullback f g).presheaf.map
        (homOfLE (productRectangle_mono f g i j)).op := by
  change X.presheaf.map i.op ≫ (pullback.fst f g).appLE U' _ inf_le_left =
    (pullback.fst f g).appLE U _ inf_le_left ≫ _
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem productRectangleRightMap_restrict :
    Y.presheaf.map j.op ≫ CubeProductSections.Construction.CubeCech.productRectangleRightMap f g U' V' =
      CubeProductSections.Construction.CubeCech.productRectangleRightMap f g U V ≫ (pullback f g).presheaf.map
        (homOfLE (productRectangle_mono f g i j)).op := by
  change Y.presheaf.map j.op ≫ (pullback.snd f g).appLE V' _ inf_le_right =
    (pullback.snd f g).appLE V _ inf_le_right ≫ _
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem productRectangleSectionsEquiv_restrict
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hU' : IsAffineOpen U') (hV' : IsAffineOpen V')
    (z : CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra f U ⊗[k] CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra g V) :
    CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv f g U' V' hU' hV'
      (TensorProduct.map (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsRestrictionAlgHom f i).toLinearMap
        (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsRestrictionAlgHom g j).toLinearMap z) =
      (pullback f g).presheaf.map (homOfLE (productRectangle_mono f g i j)).op
        (CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv f g U V hU hV z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x y =>
    rw [TensorProduct.map_tmul, CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv_tmul,
      CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv_tmul, map_mul]
    exact congrArg₂ (fun a b ↦ a * b)
      (congrArg (fun q : Γ(X, U) ⟶ Γ(pullback f g, CubeProductSections.Construction.CubeCech.productRectangle f g U' V') ↦ q x)
        (productRectangleLeftMap_restrict f g i j))
      (congrArg (fun q : Γ(Y, V) ⟶ Γ(pullback f g, CubeProductSections.Construction.CubeCech.productRectangle f g U' V') ↦ q y)
        (productRectangleRightMap_restrict f g i j))

theorem productRectangleModuleSectionsEquiv_restrict
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hU' : IsAffineOpen U') (hV' : IsAffineOpen V')
    (z : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) ⊗[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U' V' hU' hV'
      (TensorProduct.map ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.map i.op).hom
        ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.map j.op).hom z) =
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.map
        (homOfLE (productRectangle_mono f g i j)).op
          (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V hU hV z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x y =>
    change CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv f g U' V' hU' hV'
      (X.presheaf.map i.op x ⊗ₜ[k] Y.presheaf.map j.op y) =
      (pullback f g).presheaf.map (homOfLE (productRectangle_mono f g i j)).op
        (CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y))
    exact productRectangleSectionsEquiv_restrict f g i j hU hV hU' hV' (x ⊗ₜ[k] y)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech
