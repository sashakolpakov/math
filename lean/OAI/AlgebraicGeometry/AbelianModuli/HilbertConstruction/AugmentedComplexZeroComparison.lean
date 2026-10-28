import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Augmented Complex Zero Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedComplexZeroComparison.IntrinsicCech.AugmentedZero

noncomputable section

/-! Degree-zero comparison for an exact augmented complex and its naturality. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
private theorem two_squares {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (g₁ : B₀ ⟶ B₁) (g₂ : B₁ ⟶ B₂)
    (z₀ : A₀ ⟶ B₀) (z₁ : A₁ ⟶ B₁) (z₂ : A₂ ⟶ B₂)
    (h₁ : z₀ ≫ g₁ = f₁ ≫ z₁) (h₂ : z₁ ≫ g₂ = f₂ ≫ z₂) :
    z₀ ≫ (g₁ ≫ g₂) = (f₁ ≫ f₂) ≫ z₂ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

def comparison (K : CochainComplex C ℕ) {A : C}
    (a : A ⟶ K.X 0) (w : a ≫ K.d 0 1 = 0) [Mono a]
    (h : (ShortComplex.mk a (K.d 0 1) w).Exact) : K.homology 0 ≅ A := by
  let l := K.liftCycles a 1 (by simp) w
  have : IsIso l := (CochainComplex.isIso_liftCycles_iff K a w).mpr ⟨h, inferInstance⟩
  exact K.isoHomologyπ₀.symm ≪≫ (asIso l).symm

theorem naturality {K L : CochainComplex C ℕ} {A B : C}
    (a : A ⟶ K.X 0) (wa : a ≫ K.d 0 1 = 0) [Mono a]
    (b : B ⟶ L.X 0) (wb : b ≫ L.d 0 1 = 0) [Mono b]
    (ha : (ShortComplex.mk a (K.d 0 1) wa).Exact)
    (hb : (ShortComplex.mk b (L.d 0 1) wb).Exact)
    (f : A ⟶ B) (ψ : K ⟶ L) (hψ : f ≫ b = a ≫ ψ.f 0) :
    HomologicalComplex.homologyMap ψ 0 ≫ (comparison L b wb hb).hom =
      (comparison K a wa ha).hom ≫ f := by
  let aK := K.liftCycles a 1 (by simp) wa
  let aL := L.liftCycles b 1 (by simp) wb
  have : IsIso aK := (CochainComplex.isIso_liftCycles_iff K a wa).mpr ⟨ha, inferInstance⟩
  have : IsIso aL := (CochainComplex.isIso_liftCycles_iff L b wb).mpr ⟨hb, inferInstance⟩
  let m := HomologicalComplex.cyclesMap ψ 0
  have h : aK ≫ m = f ≫ aL := by
    apply (cancel_mono (L.iCycles 0)).mp
    dsimp only [aK, aL, m]
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, HomologicalComplex.liftCycles_i,
      Category.assoc, HomologicalComplex.liftCycles_i]
    exact hψ.symm
  have hi : m ≫ (asIso aL).inv = (asIso aK).inv ≫ f := by
    change m ≫ inv aL = inv aK ≫ f
    apply (cancel_epi aK).mp
    rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  exact two_squares K.isoHomologyπ₀.inv (asIso aK).inv L.isoHomologyπ₀.inv (asIso aL).inv
    (HomologicalComplex.homologyMap ψ 0) m f
    (CochainComplex.isoHomologyπ₀_inv_naturality ψ) hi

def comparisonWithIso (K : CochainComplex C ℕ) {A A' : C}
    (a : A ⟶ K.X 0) (w : a ≫ K.d 0 1 = 0) [Mono a]
    (h : (ShortComplex.mk a (K.d 0 1) w).Exact) (q : A ≅ A') : K.homology 0 ≅ A' :=
  comparison K a w h ≪≫ q

theorem naturalityWithIso {K L : CochainComplex C ℕ} {A B A' B' : C}
    (a : A ⟶ K.X 0) (wa : a ≫ K.d 0 1 = 0) [Mono a]
    (b : B ⟶ L.X 0) (wb : b ≫ L.d 0 1 = 0) [Mono b]
    (ha : (ShortComplex.mk a (K.d 0 1) wa).Exact)
    (hb : (ShortComplex.mk b (L.d 0 1) wb).Exact)
    (f : A ⟶ B) (ψ : K ⟶ L) (hψ : f ≫ b = a ≫ ψ.f 0)
    (q : A ≅ A') (r : B ≅ B') (g : A' ⟶ B') (hg : f ≫ r.hom = q.hom ≫ g) :
    HomologicalComplex.homologyMap ψ 0 ≫ (comparisonWithIso L b wb hb r).hom =
      (comparisonWithIso K a wa ha q).hom ≫ g :=
  two_squares (comparison K a wa ha).hom q.hom (comparison L b wb hb).hom r.hom
    (HomologicalComplex.homologyMap ψ 0) f g (naturality a wa b wb ha hb f ψ hψ) hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedComplexZeroComparison.IntrinsicCech.AugmentedZero
