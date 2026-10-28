import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionCharacterNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilData

/-! # Weil Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilPairing

noncomputable section

/-! The standard Weil unit is defined over the original field through the actual inverse Cartier-Picard character, on all torsion test points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)

local instance originalHom : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom) := ell.preservesGroup
local instance originalFinite : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom).left := ell.finite
local instance originalFlat : Flat (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom).left := ell.flat
local instance originalSurjective : Surjective (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom).left := ell.surjective
/-- A torsion point remains torsion after the original polarization homomorphism. -/
theorem dual_torsion {T : Over (Spec (.of k))} (x : T ⟶ A.scheme) (hx : x ^ n = 1) :
    (x ≫ ell.hom) ^ n = 1 := by
  simpa only [MonObj.pow_comp, MonObj.one_comp] using congrArg (fun z => z ≫ ell.hom) hx

/-- Actual Cartier-Picard inversion and evaluation give the regular unit of the standard Weil pairing. -/
def value {T : Over (Spec (.of k))} (x : T ⟶ A.scheme) (hx : x ^ n = 1)
    (y : T ⟶ A.scheme) (hy : y ^ n = 1) : Γ(T.left, ⊤)ˣ := by
  have hcover := Reference.Torsion.cover D ell n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hcover.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hcover.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hcover.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hcover.2.2.2.1
  exact TorsionCharacterNaturality.source_value A.scheme (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) ell.hom n hn
    (Canonical.WeilData.representative D ell n hn) x hx y hy

/-- The actual pairing is natural on every test scheme, including nonreduced ones. -/
theorem natural {T U : Over (Spec (.of k))} (f : U ⟶ T)
    (x : T ⟶ A.scheme) (hx : x ^ n = 1) (hxf : (f ≫ x) ^ n = 1)
    (y : T ⟶ A.scheme) (hy : y ^ n = 1) (hyf : (f ≫ y) ^ n = 1) :
    value D ell n hn (f ≫ x) hxf (f ≫ y) hyf = Units.map f.left.appTop.hom (value D ell n hn x hx y hy) := by
  have hcover := Reference.Torsion.cover D ell n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hcover.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hcover.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hcover.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hcover.2.2.2.1
  exact TorsionCharacterNaturality.source_value_natural A.scheme (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) ell.hom n hn
    (Canonical.WeilData.representative D ell n hn) f x hx hxf y hy hyf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilPairing
