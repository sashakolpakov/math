import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductPoints

/-! # Product Factorization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductFactorization.Construction

noncomputable section

/-! Native product maps factor on every test scheme exactly when their
components factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme}

theorem groupPairMap_factor_iff {G H G' H' : Grp (Over S)} (i : G' ⟶ G) (j : H' ⟶ H)
    (T : Over S) (a : T ⟶ (G ⊗ H).X) :
    (∃ z : T ⟶ (G' ⊗ H').X, z ≫ (i ⊗ₘ j).hom.hom = a) ↔
      (∃ x : T ⟶ G'.X, x ≫ i.hom.hom = a ≫ fst G.X H.X) ∧
      (∃ y : T ⟶ H'.X, y ≫ j.hom.hom = a ≫ snd G.X H.X) := by
  constructor
  · rintro ⟨z, rfl⟩
    constructor
    · refine ⟨z ≫ fst G'.X H'.X, ?_⟩
      exact (Category.assoc z (fst G'.X H'.X) i.hom.hom).trans
        ((congrArg (fun f => z ≫ f) (tensorHom_fst i.hom.hom j.hom.hom).symm).trans
          (Category.assoc z (i ⊗ₘ j).hom.hom (fst G.X H.X)).symm)
    · refine ⟨z ≫ snd G'.X H'.X, ?_⟩
      exact (Category.assoc z (snd G'.X H'.X) j.hom.hom).trans
        ((congrArg (fun f => z ≫ f) (tensorHom_snd i.hom.hom j.hom.hom).symm).trans
          (Category.assoc z (i ⊗ₘ j).hom.hom (snd G.X H.X)).symm)
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨lift x y, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · change (lift x y ≫ (i.hom.hom ⊗ₘ j.hom.hom)) ≫ fst G.X H.X = _
      rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
      exact hx
    · change (lift x y ≫ (i.hom.hom ⊗ₘ j.hom.hom)) ≫ snd G.X H.X = _
      rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd]
      exact hy

theorem groupBlockProductMap_factor_iff (n : ℕ) (G H : Fin n → Grp (Over S))
    (i : ∀ v, G v ⟶ H v) (T : Over S) (a : T ⟶ (BlockProducts.Construction.groupBlockProduct n H).X) :
    (∃ z : T ⟶ (BlockProducts.Construction.groupBlockProduct n G).X, z ≫ (BlockProducts.Construction.groupBlockProductMap n G H i).hom.hom = a) ↔
      ∀ v : Fin n, ∃ z : T ⟶ (G v).X,
        z ≫ (i v).hom.hom = ProductPoints.Construction.groupBlockProductPointsEquiv n H T a v := by
  constructor
  · rintro ⟨z, rfl⟩ v
    exact ⟨ProductPoints.Construction.groupBlockProductPointsEquiv n G T z v,
      (ProductPoints.Construction.groupBlockProductPointsEquiv_map n G H i T z v).symm⟩
  · intro h
    choose z hz using h
    let a' := (ProductPoints.Construction.groupBlockProductPointsEquiv n G T).symm z
    refine ⟨a', ?_⟩
    apply (ProductPoints.Construction.groupBlockProductPointsEquiv n H T).injective
    funext v
    exact (ProductPoints.Construction.groupBlockProductPointsEquiv_map n G H i T a' v).trans
      ((congrArg (fun f => f v ≫ (i v).hom.hom)
        ((ProductPoints.Construction.groupBlockProductPointsEquiv n G T).apply_symm_apply z)).trans (hz v))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductFactorization.Construction
