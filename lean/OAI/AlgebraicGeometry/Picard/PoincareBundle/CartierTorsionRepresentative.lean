import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing

/-! # Cartier Torsion Representative -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierTorsionRepresentative

noncomputable section

/-! Actual Cartier characters representing every dual torsion point, including infinitesimal parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
  [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

/-- The actual finite-group-scheme Cartier-Picard isomorphism. -/
def cartierIso : C.dual ≅ AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk D.withPicardGroup.abelian) n :=
  @asIso _ _ _ _
    (AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D.withPicardGroup C n (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n))
    (AbelianScheme.CartierDuality.RelativeIso.Construction.KernelCharacters.relativeMultiplicationCartierToPicardTorsionGroup_isIso A D ell n hn C)

/-- Inverting actual Cartier-Picard descent constructs the character of a dual torsion point. -/
def representative {T : Over S} (y : T ⟶ D.withPicardGroup.abelian) (hy : y ^ n = 1) : T ⟶ C.dual.X :=
  AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n y hy ≫ (cartierIso A D ell n hn C).inv.hom.hom

/-- The constructed character recovers the original torsion lift as an actual scheme map. -/
theorem representative_torsion {T : Over S} (y : T ⟶ D.withPicardGroup.abelian) (hy : y ^ n = 1) :
    representative A D ell n hn C y hy ≫
      AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) D.withPicardGroup n (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C =
        AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n y hy := by
  have h := congrArg (fun f => f.hom.hom) (cartierIso A D ell n hn C).inv_hom_id
  change (cartierIso A D ell n hn C).inv.hom.hom ≫
    AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) D.withPicardGroup n (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C = 𝟙 _ at h
  change (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n y hy ≫ (cartierIso A D ell n hn C).inv.hom.hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n y hy ≫ z) h).trans (Category.comp_id _))

/-- The Cartier character's actual Poincare point is exactly the supplied dual point. -/
theorem representative_point {T : Over S} (y : T ⟶ D.withPicardGroup.abelian) (hy : y ^ n = 1) :
    AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A) ^ n) T
      (C.sectionEquiv T (representative A D ell n hn C y hy)) D.withPicardGroup = y := by
  rw [← AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply, ← AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion ((𝟙 A) ^ n)
    D.withPicardGroup n (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C, ← Category.assoc,
    representative_torsion]
  exact AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n y hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierTorsionRepresentative
