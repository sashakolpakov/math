import OAI.AlgebraicGeometry.PELModuli.CMPoints.CharacterRetracts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffinePullback
import OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters

/-! # Base Characters -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BaseCharacters

noncomputable section

/-! Characters over the base scheme are actual group-scheme
homomorphisms. For an FiniteEtale affine presentation these are precisely its
grouplike coordinate characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def cartierCharactersIso {S : Scheme.{0}} {F G : (Over S)ᵒᵖ ⥤ GrpCat} (e : F ≅ G) :
    DualityPairing.cartierCharacters F ≅ DualityPairing.cartierCharacters G :=
  { hom := DualityPairing.restrictCharacters e.inv
    inv := DualityPairing.restrictCharacters e.hom
    hom_inv_id := by rw [← CharacterRetracts.restrictCharacters_comp, e.hom_inv_id, CharacterRetracts.restrictCharacters_id]
    inv_hom_id := by rw [← CharacterRetracts.restrictCharacters_comp, e.inv_hom_id, CharacterRetracts.restrictCharacters_id] }

def baseCharactersEquiv {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ GrpCat) :
    (DualityPairing.cartierCharacters F).obj (.op (Over.mk (𝟙 S))) ≃
      (F ⟶ yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) :=
  (Equivalence.congrLeft (Over.equivalenceOfIsTerminal (Over.mkIdTerminal (X := S))).op).fullyFaithfulInverse.homEquiv.symm

def groupBaseCharactersEquiv {S : Scheme.{0}} (G : Grp (Over S)) :
    (DualityPairing.cartierCharacters (yonedaGrp.obj G)).obj (.op (Over.mk (𝟙 S))) ≃
      (G ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) :=
  (baseCharactersEquiv (yonedaGrp.obj G)).trans yonedaGrpFullyFaithful.homEquiv.symm

def affineBaseCharactersEquiv (k : Type) [Field k] (G : Grp (Over (Spec (.of k)))) :
    (DualityPairing.cartierCharacters (yonedaGrp.obj G)).obj (.op (Over.mk (𝟙 (Spec (.of k))))) ≃
      (G ⟶ AbelianScheme.CartierDuality.Characters.Construction.multiplicativeGroupScheme k) :=
  (groupBaseCharactersEquiv G).trans
    (AbelianScheme.CartierDuality.AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso k).homToEquiv

def coordinateHopfGroupIso {k : Type} [Field k] (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) :
    letI := G.coordinateHopf
    AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme k G.algebra ≅ Grp.mk G.scheme := by
  letI := G.coordinateHopf
  let : (algSpec (CommRingCat.of k)).Braided := braidedAlgSpec
  refine Grp.mkIso (Iso.refl _) ?_ ?_
  · apply Over.OverMorphism.ext
    change (η[(AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme k G.algebra).X]).left ≫ 𝟙 _ = _
    rw [Category.comp_id]
    have h := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage
      (Functor.OplaxMonoidal.η (algSpec (CommRingCat.of k)) ≫ η[G.scheme])
    have hc := congrArg (fun f => Functor.LaxMonoidal.ε (algSpec (CommRingCat.of k)) ≫ f) h
    simp only [Functor.Monoidal.ε_η_assoc] at hc
    exact congrArg Over.Hom.left hc
  · apply Over.OverMorphism.ext
    change (μ[(AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme k G.algebra).X]).left ≫ 𝟙 _ =
      ((𝟙 G.scheme) ⊗ₘ (𝟙 G.scheme)).left ≫ (μ[G.scheme]).left
    have ht : ((𝟙 G.scheme) ⊗ₘ (𝟙 G.scheme)).left = 𝟙 _ := by
      rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight]
      rfl
    have hm : (μ[(AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme k G.algebra).X]).left =
        (μ[G.scheme]).left := G.coordinateHopf_represents_mul
    exact (Category.comp_id _).trans (hm.trans
      ((congrArg (fun f => f ≫ (μ[G.scheme]).left) ht).trans (Category.id_comp _)).symm)

def finiteGroupBaseCharactersEquiv {k : Type} [Field k]
    (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) :
    (DualityPairing.cartierCharacters (yonedaGrp.obj (Grp.mk G.scheme))).obj
      (.op (Over.mk (𝟙 (Spec (.of k))))) ≃ G.characterGroup := by
  letI := G.coordinateHopf
  exact (affineBaseCharactersEquiv k (Grp.mk G.scheme)).trans
    ((coordinateHopfGroupIso G).homFromEquiv.symm.trans
      (AbelianScheme.CartierDuality.Characters.Construction.groupLikeEquivSchemeCharacters k G.algebra).symm)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BaseCharacters
