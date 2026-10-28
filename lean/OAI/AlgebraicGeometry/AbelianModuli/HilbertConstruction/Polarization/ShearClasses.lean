import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ClassPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ShearIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.ShearClasses

/-! # Shear Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ShearClasses

noncomputable section

/-! The actual polarization bundle classes transform under product swaps
and integer shears by the quadratic change-of-variables formulas. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]

def polarizationSquareClass (a b c : ℤ) : Line.Bundles.LineBundle.IsoClass (A.scheme ⊗ A.scheme).left :=
  let B := ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme)
  let x := fst A.scheme A.scheme
  let y := snd A.scheme A.scheme
  B x x ^ a * B y y ^ b * B x y ^ c

theorem polarizationSquareClass_as_bundles (a b c : ℤ) :
    polarizationSquareClass D p a b c =
      Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (fst A.scheme A.scheme).left) ^ a *
        Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (snd A.scheme A.scheme).left) ^ b *
        (Line.Bundles.LineBundle.classOf (D.poincareAt p) : Line.Bundles.LineBundle.IsoClass (A.scheme ⊗ A.scheme).left) ^ c := by
  rw [ClassPairing.graphPullback_class_eq_pair, ClassPairing.graphPullback_class_eq_pair, ClassPairing.poincareAt_class_eq_pair_projections]
  rfl

variable (L : Line.Bundles.LineBundle A.scheme.left)
variable (e : (((D.poincareAt p).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
  (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)

include L e in
theorem polarizationSquareClass_pullback_shear (a b c t : ℤ) :
    Line.Bundles.LineBundle.pullbackClass (Product.ShearIsomorphisms.productShearIso A.scheme t).hom.left (polarizationSquareClass D p a b c) =
      polarizationSquareClass D p a (b + t * c + t ^ 2 * a) (c + 2 * t * a) := by
  let B := ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme)
  let x := fst A.scheme A.scheme
  let y := snd A.scheme A.scheme
  let h := (Product.ShearIsomorphisms.productShearIso A.scheme t).hom
  let r := Line.Bundles.LineBundle.pullbackClassMonoidHom h.left
  have hs (u v : A.scheme ⊗ A.scheme ⟶ A.scheme) : B u v = B v u :=
    PairSymmetry.polarizationPairClass_symmetric D p L e u v
  have hx : r (B x x) = B x x * B y y ^ (t ^ 2) * B x y ^ (2 * t) := by
    change Line.Bundles.LineBundle.pullbackClass h.left (B x x) = _
    rw [ClassPairing.polarizationPairClass_naturality]
    change B (h ≫ x) (h ≫ x) = _
    rw [Product.ShearIsomorphisms.productShearIso_hom_fst]
    exact Bilinear.ShearClasses.symmetric_bilinear_shear_square B hs x y t
  have hy : r (B y y) = B y y := by
    change Line.Bundles.LineBundle.pullbackClass h.left (B y y) = _
    rw [ClassPairing.polarizationPairClass_naturality]
    change B (h ≫ y) (h ≫ y) = _
    rw [Product.ShearIsomorphisms.productShearIso_hom_snd]
  have hxy : r (B x y) = B x y * B y y ^ t := by
    change Line.Bundles.LineBundle.pullbackClass h.left (B x y) = _
    rw [ClassPairing.polarizationPairClass_naturality]
    change B (h ≫ x) (h ≫ y) = _
    rw [Product.ShearIsomorphisms.productShearIso_hom_fst, Product.ShearIsomorphisms.productShearIso_hom_snd]
    exact Bilinear.ShearClasses.bilinear_shear_cross B x y t
  change r (B x x ^ a * B y y ^ b * B x y ^ c) =
    B x x ^ a * B y y ^ (b + t * c + t ^ 2 * a) * B x y ^ (c + 2 * t * a)
  rw [r.map_mul, r.map_mul, r.map_zpow, r.map_zpow, r.map_zpow, hx, hy, hxy]
  exact Bilinear.ShearClasses.shear_three_class_powers (B x x) (B y y) (B x y) a b c t

include L e in
theorem polarizationSquareClass_pullback_swap (a b c : ℤ) :
    Line.Bundles.LineBundle.pullbackClass (Product.ShearIsomorphisms.productSwapIso A.scheme).hom.left (polarizationSquareClass D p a b c) =
      polarizationSquareClass D p b a c := by
  let B := ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme)
  let x := fst A.scheme A.scheme
  let y := snd A.scheme A.scheme
  let h := (Product.ShearIsomorphisms.productSwapIso A.scheme).hom
  let r := Line.Bundles.LineBundle.pullbackClassMonoidHom h.left
  have hx : r (B x x) = B y y := by
    change Line.Bundles.LineBundle.pullbackClass h.left (B x x) = _
    rw [ClassPairing.polarizationPairClass_naturality]
    change B (h ≫ x) (h ≫ x) = _
    rw [Product.ShearIsomorphisms.productSwapIso_hom_fst]
  have hy : r (B y y) = B x x := by
    change Line.Bundles.LineBundle.pullbackClass h.left (B y y) = _
    rw [ClassPairing.polarizationPairClass_naturality]
    change B (h ≫ y) (h ≫ y) = _
    rw [Product.ShearIsomorphisms.productSwapIso_hom_snd]
  have hxy : r (B x y) = B x y := by
    change Line.Bundles.LineBundle.pullbackClass h.left (B x y) = _
    rw [ClassPairing.polarizationPairClass_naturality]
    change B (h ≫ x) (h ≫ y) = _
    rw [Product.ShearIsomorphisms.productSwapIso_hom_fst, Product.ShearIsomorphisms.productSwapIso_hom_snd]
    exact PairSymmetry.polarizationPairClass_symmetric D p L e y x
  change r (B x x ^ a * B y y ^ b * B x y ^ c) = B x x ^ b * B y y ^ a * B x y ^ c
  rw [r.map_mul, r.map_mul, r.map_zpow, r.map_zpow, r.map_zpow, hx, hy, hxy]
  ac_rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ShearClasses
