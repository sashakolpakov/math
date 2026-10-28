import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange

/-! # Compact Subgroup Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactSubgroupBaseChange.Construction

noncomputable section

/-! Literal whole and identity subgroups retain their native embedded
representatives under base change and an ambient group isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes

variable {S S' : Scheme} (s : S' ⟶ S)
variable {H G : Grp (Over S)} {J G' : Grp (Over S')}
variable (i : H ⟶ G) (j : J ⟶ G') (a : (Over.pullback s).mapGrp.obj G ≅ G') (b : Bool)
variable (hH : ∀ (T : Over S) (z : T ⟶ G.X),
  (∃ x : T ⟶ H.X, x ≫ i.hom.hom = z) ↔ if b then True else z = 1)
variable (hJ : ∀ (T : Over S') (z : T ⟶ G'.X),
  (∃ x : T ⟶ J.X, x ≫ j.hom.hom = z) ↔ if b then True else z = 1)

include hH hJ

theorem compactPointImage_baseChange (T : Over S') (z : T ⟶ G'.X) :
    (∃ x : T ⟶ (Over.pullback s).obj H.X,
      x ≫ ((Over.pullback s).map i.hom.hom ≫ a.hom.hom.hom) = z) ↔
      ∃ y : T ⟶ J.X, y ≫ j.hom.hom = z := by
  let ep := CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G T
  let ea := ((yonedaGrp.mapIso a).app (.op T)).groupIsoToMulEquiv
  let e := (ep.trans ea).symm
  have hz : e z = 1 ↔ z = 1 :=
    ⟨fun h => e.injective (h.trans e.map_one.symm), fun h => (congrArg e h).trans e.map_one⟩
  have hb : (if b then True else e z = 1) ↔ (if b then True else z = 1) := by
    cases b
    · exact hz
    · rfl
  have hi := EmbeddedBaseChange.Construction.pointImage_postcomp_iso ((Over.pullback s).map i.hom.hom)
    ((Grp.forget (Over S')).mapIso a) z
  have hp := EmbeddedBaseChange.Construction.pointImage_baseChange s i.hom.hom T (z ≫ a.inv.hom.hom)
  exact hi.trans (hp.trans ((hH ((Over.map s).obj T) (e z)).trans (hb.trans (hJ T z).symm)))

variable [Mono i.hom.hom] [Mono j.hom.hom]

theorem exists_compactSubgroupBaseChangeIso :
    ∃ e : (Over.pullback s).obj H.X ≅ J.X,
      e.hom ≫ j.hom.hom = (Over.pullback s).map i.hom.hom ≫ a.hom.hom.hom := by
  have : Mono ((Over.pullback s).map i.hom.hom) := inferInstance
  have : IsIso a.hom.hom.hom := inferInstanceAs (IsIso ((Grp.forget (Over S')).map a.hom))
  have : Mono ((Over.pullback s).map i.hom.hom ≫ a.hom.hom.hom) :=
    mono_comp' (inferInstanceAs (Mono ((Over.pullback s).map i.hom.hom)))
      (inferInstanceAs (Mono a.hom.hom.hom))
  exact EmbeddedBaseChange.Construction.exists_samePointImageIso _ _ (compactPointImage_baseChange s i j a b hH hJ)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactSubgroupBaseChange.Construction
