import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierPairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeAnnihilator
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

/-! # Cartier Annihilator Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierAnnihilatorComparison

noncomputable section

/-! FrobeniusKernel's independently defined kernel of character restriction is
exactly the relative annihilator for its constructed scheme pairing.
The equality is on arbitrary test schemes, including nonreduced ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierPairing

variable {R : CommRingCat.{u}} {G H : Grp (Over (Spec R))} {B : Over (Spec R)}
variable (P : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates R G) (Q : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates R H) (i : H ⟶ G)

theorem cartier_annihilator_family :
    (CartierPairing.cartierPairing P).relativeAnnihilator (Kernel.Base.fixedKernelFamily (P := B) i.hom.hom) =
      Kernel.Base.fixedKernelFamily (P := B) (P.annihilatorInclusion Q i).hom.hom := by
  ext T t b
  constructor
  · intro hb
    have hχ : Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ P.pointsEquiv T b = 1 := by
      apply (CartierPairing.restricted_character_eq_one_iff i T (P.pointsEquiv T b)).mpr
      intro U f a
      have h := hb U f (a ≫ i.hom.hom) ⟨a, rfl⟩
      rw [CartierPairing.cartierPairing_pairValue, CartierPairing.cartierPairValue, CartierPairing.pointCharacters_natural] at h
      exact h
    obtain ⟨a, ha, _⟩ := (P.annihilator_universal Q i T b).mp hχ
    exact ⟨a, ha⟩
  · intro hb
    obtain ⟨a, ha⟩ := hb
    have hχ := (P.annihilator_universal Q i T b).mpr
      ⟨a, ha, fun a' ha' => (cancel_mono (P.annihilatorInclusion Q i).hom.hom).mp (ha'.trans ha.symm)⟩
    intro U f c hc
    obtain ⟨z, rfl⟩ := hc
    change (CartierPairing.cartierPairing P).pairValue (z ≫ i.hom.hom) (f ≫ b) = 1
    rw [CartierPairing.cartierPairing_pairValue, CartierPairing.cartierPairValue, CartierPairing.pointCharacters_natural]
    exact (CartierPairing.restricted_character_eq_one_iff i T (P.pointsEquiv T b)).mp hχ U f z

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierAnnihilatorComparison
