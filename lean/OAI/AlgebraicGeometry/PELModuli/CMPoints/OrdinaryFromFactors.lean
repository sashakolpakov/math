import OAI.AlgebraicGeometry.PELModuli.CMPoints.ProductCharacters
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightOneCounts
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityCanonicalPairing
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EtaleRank

/-! # Ordinary From Factors -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactors

noncomputable section

/-! An actual decomposition of polarized abelian q-torsion into
height-one FiniteEtale factors implies the ordinary geometric point count.
The Cartier character identifications are constructed, not assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k I : Type} [Field k] [IsAlgClosed k] [Fintype I]
  {q : ℕ} [Fact q.Prime] [CharP k q]

def finiteGroupPointFunctor (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) :
    (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat :=
  AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction.Schemes.commGroupPoints (Spec (.of k)) (Grp.mk G.scheme)

def finiteGroupBasePointsEquiv (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) :
    (finiteGroupPointFunctor G).obj (.op (Over.mk (𝟙 (Spec (.of k))))) ≃ G.rationalPoints :=
  (Iso.homCongr (EtaleRank.affineFieldBaseIso k) (Iso.refl G.scheme)).symm

theorem ordinary_count_of_torsion_heightOne_decomposition_of_character_iso
    {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (d : DualityPairing.TorsionCharacterIso P q)
    [IsIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P q)
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ d.hom)]
    (G : I → GroupSchemes.FiniteEtale.PDivisibleGroup k q 1) (hI : Fintype.card I = 2 * g)
    (e : P.abelian.torsionFunctor q ≅
      FlattenTorsionFactors.piGroupFunctor (fun i => finiteGroupPointFunctor ((G i).level 1))) :
    Nat.card (P.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  let X := P.abelian.torsionPoints q T
  let Y := (DualityPairing.cartierCharacters (P.abelian.torsionFunctor q)).obj (.op T)
  let ep : X ≃ (∀ i, ((G i).level 1).rationalPoints) :=
    (Equiv.ofBijective (e.hom.app (.op T)) (ConcreteCategory.bijective_of_isIso _)).trans
      (Equiv.piCongrRight (fun i => finiteGroupBasePointsEquiv ((G i).level 1)))
  let ec : Y ≃ (∀ i, ((G i).level 1).characterGroup) :=
    (Equiv.ofBijective ((BaseCharacters.cartierCharactersIso e).hom.app (.op T))
      (ConcreteCategory.bijective_of_isIso _)).trans
      ((ProductCharacters.piBaseCharactersEquiv (fun i => finiteGroupPointFunctor ((G i).level 1))).trans
        (Equiv.piCongrRight (fun i => BaseCharacters.finiteGroupBaseCharactersEquiv ((G i).level 1))))
  let selfDual := asIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P q)
    (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ d.hom)
  let ed : X ≃ Y := Equiv.ulift.symm.trans
    (Equiv.ofBijective (selfDual.hom.app (.op T)) (ConcreteCategory.bijective_of_isIso _))
  exact HeightOneCounts.ordinary_count_of_selfDual_heightOne_factors G g hI ep ec ed

theorem ordinary_count_of_torsion_heightOne_decomposition
    {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (hgood : q.Coprime (∏ i, δ i))
    (G : I → GroupSchemes.FiniteEtale.PDivisibleGroup k q 1) (hI : Fintype.card I = 2 * g)
    (e : P.abelian.torsionFunctor q ≅
      FlattenTorsionFactors.piGroupFunctor (fun i => finiteGroupPointFunctor ((G i).level 1))) :
    Nat.card (P.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g := by
  let d := CartierDualityCanonicalPairing.geometricTorsionCharacterIso P q (Fact.out : q.Prime).pos
  have : IsIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P q)
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ d.hom) :=
    CartierDualityCanonicalPairing.geometricTorsionCharacter_perfect P q (Fact.out : q.Prime).pos hgood
  exact ordinary_count_of_torsion_heightOne_decomposition_of_character_iso P d G hI e

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactors
