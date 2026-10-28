import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageDominance

/-! # Scheme Dominance -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.SchemeDominance

noncomputable section

/-! Products of quasi-compact scheme-theoretically dominant maps
remain scheme-theoretically dominant when the complementary factors
are flat over the base. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

namespace Construction

universe u
variable {S : Scheme.{u}}

theorem tensorRight_schemeDominant (A : Over S) [Flat A.hom] {T U : Over S} (j : U ⟶ T)
    [IsSchemeTheoreticallyDominant j.left] [QuasiCompact j.left] :
    IsSchemeTheoreticallyDominant (j ⊗ₘ 𝟙 A).left := by
  have : Flat (fst T A).left := inferInstanceAs (Flat (pullback.fst T.hom A.hom))
  exact IsSchemeTheoreticallyDominant.of_isPullback (Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j).flip

theorem tensorLeft_isPullback (A : Over S) {T U : Over S} (j : U ⟶ T) :
    IsPullback (𝟙 A ⊗ₘ j).left (snd A U).left (snd A T).left j.left := by
  have hs : (𝟙 A ⊗ₘ j).left ≫ (snd A T).left = (snd A U).left ≫ j.left :=
    congrArg Over.Hom.left (tensorHom_snd (𝟙 A) j)
  have hf : (𝟙 A ⊗ₘ j).left ≫ (fst A T).left = (fst A U).left := by
    have h := congrArg Over.Hom.left (tensorHom_fst (𝟙 A) j)
    change (𝟙 A ⊗ₘ j).left ≫ (fst A T).left = (fst A U).left ≫ 𝟙 A.left at h
    rw [Category.comp_id] at h
    exact h
  apply IsPullback.of_right (t := IsPullback.of_hasPullback A.hom T.hom) ?_ hs
  change IsPullback ((𝟙 A ⊗ₘ j).left ≫ (fst A T).left) (snd A U).left A.hom (j.left ≫ T.hom)
  rw [hf, j.w]
  exact IsPullback.of_hasPullback A.hom U.hom

theorem tensorLeft_schemeDominant (A : Over S) [Flat A.hom] {T U : Over S} (j : U ⟶ T)
    [IsSchemeTheoreticallyDominant j.left] [QuasiCompact j.left] :
    IsSchemeTheoreticallyDominant (𝟙 A ⊗ₘ j).left := by
  have : Flat (snd A T).left := inferInstanceAs (Flat (pullback.snd A.hom T.hom))
  exact IsSchemeTheoreticallyDominant.of_isPullback (tensorLeft_isPullback A j).flip

theorem tensorMap_schemeDominant {X X' Y Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsSchemeTheoreticallyDominant f.left] [QuasiCompact f.left]
    [IsSchemeTheoreticallyDominant g.left] [QuasiCompact g.left] [Flat Y.hom] [Flat X'.hom] :
    IsSchemeTheoreticallyDominant (f ⊗ₘ g).left := by
  have := tensorRight_schemeDominant Y f
  have := tensorLeft_schemeDominant X' g
  have he : f ⊗ₘ g = (f ⊗ₘ 𝟙 Y) ≫ (𝟙 X' ⊗ₘ g) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [he]
  change IsSchemeTheoreticallyDominant ((f ⊗ₘ 𝟙 Y).left ≫ (𝟙 X' ⊗ₘ g).left)
  infer_instance

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.SchemeDominance
