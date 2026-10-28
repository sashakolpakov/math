import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Sheaf Cover Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafCoverIso

noncomputable section

/-! A morphism of sheaves is an isomorphism if its components are
bijective on a covering sieve of every test object. -/

open _root_.CategoryTheory

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type w)}

theorem sheaf_isIso_of_cover_bijective (φ : F ⟶ G)
    (h : ∀ X : C, ∃ R : Sieve X, R ∈ J X ∧
      ∀ (Y : C) (f : Y ⟶ X), R f → Function.Bijective (φ.hom.app (.op Y))) :
    IsIso φ := by
  have hi : Presheaf.IsLocallyInjective J φ.hom := by
    constructor
    intro X x y hxy
    obtain ⟨R, hR, hb⟩ := h X.unop
    refine J.superset_covering ?_ hR
    intro Y f hf
    apply (hb Y f hf).injective
    change φ.hom.app (.op Y) (F.obj.map f.op x) =
      φ.hom.app (.op Y) (F.obj.map f.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  have hs : Presheaf.IsLocallySurjective J φ.hom := by
    constructor
    intro X x
    obtain ⟨R, hR, hb⟩ := h X
    refine J.superset_covering ?_ hR
    intro Y f hf
    exact (hb Y f hf).surjective (G.obj.map f.op x)
  exact (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨hi, hs⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafCoverIso
