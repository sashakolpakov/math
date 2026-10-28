import OAI.AlgebraicGeometry.GroupSchemes.CharacterEvaluation
import OAI.AlgebraicGeometry.GroupSchemes.CharacterGenerators

/-! # Multiplicative Classification -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! The multiplicative branch as a natural isomorphism of the original geometric tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

section

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A generating coordinate character identifies every affine-valued point with a root of unity. -/
def FiniteEtale.FiniteCommGroupScheme.characterRootsEquiv (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.cartierDual.algebra]
    (t : G.characterGroup) (N : ℕ) (hgen : ∀ x : G.characterGroup, x ∈ Subgroup.zpowers t)
    (horder : orderOf t = N) (R : CommAlgCat.{u} k) :
    G.points.obj R ≃* rootsOfUnity N R :=
  (G.coordinatePoints R).symm.trans
    (@CharacterEvaluation.FiniteEtale.pointsRootsEquiv k G.algebra _ _ G.coordinateHopf
      R _ _ G.characterValue_span t N hgen horder)

/-- This is the evaluation map on the chosen coordinate character. -/
theorem FiniteEtale.FiniteCommGroupScheme.characterRootsEquiv_apply (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.cartierDual.algebra]
    (t : G.characterGroup) (N : ℕ) (hgen : ∀ x : G.characterGroup, x ∈ Subgroup.zpowers t)
    (horder : orderOf t = N) (R : CommAlgCat.{u} k) (f : G.algebra →ₐ[k] R) :
    ((G.characterRootsEquiv t N hgen horder R (G.coordinatePoints R (toConv f))).val : R) =
      f (G.characterValue t) := by
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  let := G.coordinateHopf
  change ((CharacterEvaluation.FiniteEtale.pointsRootsEquiv k G.algebra R
      G.characterValue_span t N hgen horder
      ((G.coordinatePoints R).symm (G.coordinatePoints R (toConv f)))).val : R) = _
  rw [MulEquiv.symm_apply_apply]
  exact @CharacterEvaluation.FiniteEtale.pointsRootsEquiv_apply k G.algebra _ _
    G.coordinateHopf R _ _ G.characterValue_span t N hgen horder (toConv f)

/-- Character evaluation is natural under every homomorphism of affine test algebras. -/
theorem FiniteEtale.FiniteCommGroupScheme.characterRootsEquiv_naturality (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.cartierDual.algebra]
    (t : G.characterGroup) (N : ℕ) (hgen : ∀ x : G.characterGroup, x ∈ Subgroup.zpowers t)
    (horder : orderOf t = N) {R S : CommAlgCat.{u} k} (a : R ⟶ S) (x : G.points.obj R) :
    G.characterRootsEquiv t N hgen horder S (G.points.map a x) =
      restrictRootsOfUnity a.hom N (G.characterRootsEquiv t N hgen horder R x) := by
  obtain ⟨f, rfl⟩ := (G.coordinatePoints R).surjective x
  apply Subtype.ext
  apply Units.ext
  change ((G.characterRootsEquiv t N hgen horder S
      ((algSpec (CommRingCat.of k)).map a.op ≫ G.coordinatePoints R f)).val : S) =
    a.hom ((G.characterRootsEquiv t N hgen horder R (G.coordinatePoints R f)).val : R)
  rw [← G.coordinatePoints_precomp a f.ofConv]
  exact (G.characterRootsEquiv_apply t N hgen horder S (a.hom.comp f.ofConv)).trans
    (congrArg a.hom (G.characterRootsEquiv_apply t N hgen horder R f.ofConv)).symm

omit [IsAlgClosed k] in
/-- Coordinate restriction evaluates a character after a geometric morphism. -/
theorem FiniteEtale.FiniteCommGroupScheme.characterValue_map {G H : FiniteEtale.FiniteCommGroupScheme k}
    (f : G.scheme ⟶ H.scheme) [IsMonHom f] (t : H.characterGroup) :
    G.characterValue (FiniteEtale.FiniteCommGroupScheme.characterMap f t) = FiniteEtale.FiniteCommGroupScheme.coordinateMap f (H.characterValue t) := rfl

end

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- The multiplicative identification at a given level and affine algebra. -/
def FiniteEtale.PDivisibleGroup.multiplicativeLevelPointEquiv (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra)
    (n : ℕ) (R : CommAlgCat.{u} k) :
    (G.level n).points.obj R ≃* (FiniteEtale.multiplicativeLevel k p n).obj R := by
  have := hsplit n
  exact (G.level n).characterRootsEquiv (G.compatibleCharacters hsplit n).val (p ^ n)
    (G.compatibleCharacters_generate hsplit n) (G.compatibleCharacters hsplit n).property R

/-- Naturality of the multiplicative identification on all affine algebras. -/
def FiniteEtale.PDivisibleGroup.multiplicativeLevelPointIso (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) (n : ℕ) :
    (G.level n).points ≅ FiniteEtale.multiplicativeLevel k p n :=
  NatIso.ofComponents (fun R => (G.multiplicativeLevelPointEquiv hsplit n R).toCommGrpIso) (by
    intro R S a
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    have := hsplit n
    exact (G.level n).characterRootsEquiv_naturality (G.compatibleCharacters hsplit n).val
      (p ^ n) (G.compatibleCharacters_generate hsplit n)
      (G.compatibleCharacters hsplit n).property a x)

/-- Split Cartier-dual levels give the standard multiplicative tower, with original transitions. -/
def FiniteEtale.PDivisibleGroup.multiplicativeTowerIso (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) :
    FiniteEtale.GroupTower.Iso k (G.points k) (FiniteEtale.multiplicativeTower k p) where
  levelIso := G.multiplicativeLevelPointIso hsplit
  compatibility n := by
    apply NatTrans.ext
    funext R
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    have := hsplit n
    have := hsplit (n + 1)
    obtain ⟨f, rfl⟩ := ((G.level n).coordinatePoints R).surjective x
    apply Subtype.ext
    apply Units.ext
    change (((G.level (n + 1)).characterRootsEquiv
        (G.compatibleCharacters hsplit (n + 1)).val (p ^ (n + 1))
        (G.compatibleCharacters_generate hsplit (n + 1))
        (G.compatibleCharacters hsplit (n + 1)).property R
        ((G.level n).coordinatePoints R f ≫ G.inclusion n)).val : R) =
      (((G.level n).characterRootsEquiv (G.compatibleCharacters hsplit n).val (p ^ n)
        (G.compatibleCharacters_generate hsplit n) (G.compatibleCharacters hsplit n).property R
        ((G.level n).coordinatePoints R f)).val : R)
    rw [← FiniteEtale.FiniteCommGroupScheme.coordinatePoints_postcomp (G.inclusion n) R f.ofConv]
    have hvalue := (FiniteEtale.FiniteCommGroupScheme.characterValue_map (G.inclusion n)
      (G.compatibleCharacters hsplit (n + 1)).val).symm.trans
        (congrArg (G.level n).characterValue (G.compatibleCharacters_restriction hsplit n))
    exact ((G.level (n + 1)).characterRootsEquiv_apply
      (G.compatibleCharacters hsplit (n + 1)).val (p ^ (n + 1))
      (G.compatibleCharacters_generate hsplit (n + 1))
      (G.compatibleCharacters hsplit (n + 1)).property R
      (f.ofConv.comp (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusion n)))).trans
        ((congrArg f.ofConv hvalue).trans ((G.level n).characterRootsEquiv_apply
          (G.compatibleCharacters hsplit n).val (p ^ n)
          (G.compatibleCharacters_generate hsplit n) (G.compatibleCharacters hsplit n).property R
          f.ofConv).symm)

/-- A connected first level gives the full standard multiplicative tower on all affine algebras. -/
theorem FiniteEtale.PDivisibleGroup.multiplicative_classification_of_first_local (G : FiniteEtale.PDivisibleGroup k p 1)
    (hfirst : IsLocalRing (G.level 1).algebra) :
    Nonempty (FiniteEtale.GroupTower.Iso k (G.points k) (FiniteEtale.multiplicativeTower k p)) :=
  ⟨G.multiplicativeTowerIso (G.dual_split_of_first_local hfirst)⟩

end

end OAI.AlgebraicGeometry.GroupSchemes
