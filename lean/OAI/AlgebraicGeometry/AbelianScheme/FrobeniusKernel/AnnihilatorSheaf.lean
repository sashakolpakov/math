import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryCharacters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Annihilator Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction

noncomputable section

/-!
The opposite kernel in a split ordinary block, formulated in CartierDuality's actual
fppf character sheaf. Characters vanishing on the first factor form the
character sheaf of the second factor. This includes every nonreduced test
scheme and does not replace the multiplicative factor by a constant group.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes

variable {S : Scheme.{u}}

def splitFirstInclusion (G H : Grp (Over S)) : G ⟶ G ⊗ H := by
  have : IsMonHom (1 : G.X ⟶ H.X) := by
    change IsMonHom (toUnit G.X ≫ η[H.X])
    infer_instance
  exact Grp.homMk (lift (𝟙 G.X) (1 : G.X ⟶ H.X))

def splitSecondInclusion (G H : Grp (Over S)) : H ⟶ G ⊗ H := by
  have : IsMonHom (1 : H.X ⟶ G.X) := by
    change IsMonHom (toUnit H.X ≫ η[G.X])
    infer_instance
  exact Grp.homMk (lift (1 : H.X ⟶ G.X) (𝟙 H.X))

def splitSecondProjection (G H : Grp (Over S)) : G ⊗ H ⟶ H :=
  Grp.homMk (snd G.X H.X)

theorem characterRestriction_comp {G H K : Grp (Over S)}
    (i : G ⟶ H) (j : H ⟶ K) :
    CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction j ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction i = CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (i ≫ j) := by
  apply Sheaf.hom_ext
  ext T χ
  dsimp only [CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction, CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf, presheafHom] at *
  ext U x
  change χ.app U ((x ≫ i.hom.hom) ≫ j.hom.hom) =
    χ.app U (x ≫ (i.hom.hom ≫ j.hom.hom))
  exact congrArg (fun z => χ.app U z) (Category.assoc x i.hom.hom j.hom.hom)

theorem characterRestriction_id (G : Grp (Over S)) :
    CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (𝟙 G) = 𝟙 (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G) := by
  apply Sheaf.hom_ext
  ext T χ
  dsimp only [CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction, CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf, presheafHom] at *
  ext U x
  change χ.app U (x ≫ 𝟙 G.X) = χ.app U x
  exact congrArg (fun z => χ.app U z) (Category.comp_id x)

theorem splitSecond_character_retraction (G H : Grp (Over S)) :
    CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondProjection G H) ≫
      CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H) = 𝟙 (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S H) := by
  rw [characterRestriction_comp]
  have h : splitSecondInclusion G H ≫ splitSecondProjection G H = 𝟙 H := by
    apply Grp.hom_ext
    change lift (1 : H.X ⟶ G.X) (𝟙 H.X) ≫ snd G.X H.X = 𝟙 H.X
    exact lift_snd _ _
  rw [h, characterRestriction_id]

theorem splitSecond_character_annihilates (G H : Grp (Over S)) :
    CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondProjection G H) ≫
        CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H) =
      CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondProjection G H) ≫
        CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction (G ⊗ H) G := by
  apply Sheaf.hom_ext
  ext T χ
  dsimp only [CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction, CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction, CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf, presheafHom] at *
  ext U x
  change U.unop.left ⟶ G.X at x
  change χ.app U ((x ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X)) ≫ snd G.X H.X) = 1
  have h : (x ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X)) ≫ snd G.X H.X = 1 := by
    rw [Category.assoc, lift_snd, MonObj.comp_one]
  exact (congrArg (fun z => χ.app U z) h).trans (χ.app U).hom.map_one

/-- Every section of the annihilator is reconstructed from its restriction
to the second factor. The test section is arbitrary, not geometric. -/
theorem split_character_reconstruction
    (G H : Grp (Over S)) (P : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (a : P ⟶ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (G ⊗ H))
    (ha : a ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H) =
      a ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction (G ⊗ H) G) :
    a ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H) ≫
      CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondProjection G H) = a := by
  apply Sheaf.hom_ext
  ext T x
  dsimp only [CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction, CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf, presheafHom] at *
  ext U z
  change U.unop.left ⟶ (G ⊗ H).X at z
  let χ : (Over.forget T.unop).op ⋙ yonedaGrp.obj (G ⊗ H) ⟶
      (Over.forget T.unop).op ⋙ yonedaGrp.obj (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) := a.hom.app T x
  let χU : (U.unop.left ⟶ (G ⊗ H).X) →*
      (U.unop.left ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) := (χ.app U).hom
  have hann (g : U.unop.left ⟶ G.X) :
      χU (lift g (1 : U.unop.left ⟶ H.X)) = 1 := by
    have h := congrArg (fun b => ((b.hom.app T x).app U) g) ha
    change χU (g ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X)) = 1 at h
    have hg : g ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X) =
        lift g (1 : U.unop.left ⟶ H.X) := by
      rw [comp_lift, Category.comp_id, MonObj.comp_one]
    exact (congrArg χU hg.symm).trans h
  have hz : z = lift (z ≫ fst G.X H.X) (1 : U.unop.left ⟶ H.X) *
      lift (1 : U.unop.left ⟶ G.X) (z ≫ snd G.X H.X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [MonObj.mul_comp, lift_fst, mul_one]
    · simp only [MonObj.mul_comp, lift_snd, one_mul]
  change χU ((z ≫ snd G.X H.X) ≫
    lift (1 : H.X ⟶ G.X) (𝟙 H.X)) = χU z
  rw [comp_lift, MonObj.comp_one, Category.comp_id]
  conv_rhs => rw [hz]
  rw [map_mul, hann, one_mul]

/-- The annihilator in the Cartier-character sheaf is the dual of the
second factor. In the ordinary decomposition this is the dual étale block. -/
def splitAnnihilatorSheafIso (G H : Grp (Over S)) :
    CartierDuality.CharacterSheaf.Construction.Schemes.annihilatorSheaf (splitFirstInclusion G H) ≅ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S H := by
  let r := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H)
  let z := CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction (G ⊗ H) G
  let p := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondProjection G H)
  let j := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H)
  let c := Fork.ofι p (splitSecond_character_annihilates G H)
  have hc : IsLimit c := Fork.IsLimit.ofExistsUnique (fun t => by
    refine ⟨t.ι ≫ j, ?_, ?_⟩
    · exact split_character_reconstruction G H t.pt t.ι t.condition
    · intro b hb
      change b = t.ι ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H)
      calc
        b = b ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondProjection G H) ≫
            CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H) := by
          exact (Category.comp_id b).symm.trans
            (congrArg (fun f => b ≫ f) (splitSecond_character_retraction G H).symm)
        _ = t.ι ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H) :=
          congrArg (fun f => f ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H)) hb)
  exact (equalizerIsEqualizer r z).conePointUniqueUpToIso hc

theorem splitAnnihilatorSheafIso_hom (G H : Grp (Over S)) :
    (splitAnnihilatorSheafIso G H).hom =
      equalizer.ι (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H))
        (CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction (G ⊗ H) G) ≫
          CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H) := by
  let p := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondProjection G H)
  let j := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H)
  have he : (splitAnnihilatorSheafIso G H).hom ≫ p =
      equalizer.ι (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H))
        (CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction (G ⊗ H) G) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  exact (Category.comp_id _).symm.trans
    ((congrArg (fun f => (splitAnnihilatorSheafIso G H).hom ≫ f)
      (splitSecond_character_retraction G H).symm).trans
        ((Category.assoc _ p j).symm.trans (congrArg (fun f => f ≫ j) he)))

/-- Changing coordinates by an actual group-scheme isomorphism transports
the whole character sheaf. -/
def characterSheafIso {G H : Grp (Over S)} (e : G ≅ H) :
    CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G ≅ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S H where
  hom := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction e.inv
  inv := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction e.hom
  hom_inv_id := by
    rw [characterRestriction_comp, e.hom_inv_id, characterRestriction_id]
  inv_hom_id := by
    rw [characterRestriction_comp, e.inv_hom_id, characterRestriction_id]

/-- The split-block calculation holds in the original torsion block,
with its specified splitting isomorphism, rather than only in coordinates. -/
def annihilatorSheafIsoOfSplitting (B G H : Grp (Over S)) (e : B ≅ G ⊗ H) :
    CartierDuality.CharacterSheaf.Construction.Schemes.annihilatorSheaf (splitFirstInclusion G H ≫ e.inv) ≅ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S H := by
  let r := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H ≫ e.inv)
  let z := CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction B G
  let r' := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H)
  let z' := CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction (G ⊗ H) G
  have hr : r ≫ (Iso.refl (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G)).hom =
      (characterSheafIso e).hom ≫ r' := by
    exact (Category.comp_id r).trans
      (characterRestriction_comp (splitFirstInclusion G H) e.inv).symm
  have hz : z ≫ (Iso.refl (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G)).hom =
      (characterSheafIso e).hom ≫ z' := by
    apply Sheaf.hom_ext
    ext T χ
    rfl
  let w := parallelPairIso r z r' z' (characterSheafIso e)
    (Iso.refl (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G)) hr hz
  let a := HasLimit.isoOfNatIso w
  exact a ≪≫ splitAnnihilatorSheafIso G H

theorem annihilatorSheafIsoOfSplitting_hom (B G H : Grp (Over S)) (e : B ≅ G ⊗ H) :
    (annihilatorSheafIsoOfSplitting B G H e).hom =
      equalizer.ι (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H ≫ e.inv))
        (CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction B G) ≫
          CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitSecondInclusion G H ≫ e.inv) := by
  let r := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H ≫ e.inv)
  let z := CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction B G
  let r' := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (splitFirstInclusion G H)
  let z' := CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction (G ⊗ H) G
  let w := parallelPairIso r z r' z' (characterSheafIso e)
    (Iso.refl (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G))
    ((Category.comp_id r).trans
      (characterRestriction_comp (splitFirstInclusion G H) e.inv).symm)
    (by apply Sheaf.hom_ext; ext T χ; rfl)
  have hw : (HasLimit.isoOfNatIso w).hom ≫ equalizer.ι r' z' =
      equalizer.ι r z ≫ (characterSheafIso e).hom :=
    HasLimit.isoOfNatIso_hom_π w WalkingParallelPair.zero
  change (HasLimit.isoOfNatIso w).hom ≫ (splitAnnihilatorSheafIso G H).hom = _
  rw [splitAnnihilatorSheafIso_hom, ← Category.assoc, hw, Category.assoc]
  exact congrArg (fun f => equalizer.ι r z ≫ f)
    (characterRestriction_comp (splitSecondInclusion G H) e.inv)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction
