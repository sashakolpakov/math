import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers

/-! # Character Torsion Factor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTorsionFactor

noncomputable section

/-!
# CartierDuality: the actual character-descent morphism factors through dual torsion
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

universe u

namespace Construction.Schemes

/-- If n kills every group-scheme point, it kills every section of its actual Cartier character sheaf. -/
theorem characterSection_pow_eq_one {S : Scheme.{u}} (G : Grp (Over S)) (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1) (Q : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (.op Q)) : χ ^ n = 1 := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  let E : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (.op Q) →* (U.unop.left ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
    { toFun := fun ψ => ψ.app U x
      map_one' := rfl
      map_mul' _ _ := rfl }
  exact (E.map_pow χ n).trans (((χ.app U).hom.map_pow x n).symm.trans
    ((congrArg (χ.app U) (hn U.unop.left x)).trans (χ.app U).hom.map_one))

end Construction.Schemes

namespace Construction.KernelCharacters

variable {S : Scheme.{u}}

/-- Multiplication's actual scheme-theoretic kernel is killed by n on every test scheme. -/
theorem multiplicationKernelPoint_pow (A : Over S) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) : x ^ n = 1 := by
  let f := (𝟙 A : A ⟶ A) ^ n
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  have h : (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ≫ f = 1 := by
    rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]
  simpa only [f, MonObj.comp_pow, Category.comp_id] using h

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

/-- A torsion Cartier section maps to a torsion point of the Picard-derived dual group. -/
theorem parameterCharacterDualPoint_pow (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (n : ℕ) (Q : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) (hχ : χ ^ n = 1) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D) ^ n = 1 := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  let H := ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterDualPointHom f Q D
  exact (H.map_pow χ n).symm.trans ((congrArg H hχ).trans H.map_one)

/-- The universal character line maps into dual torsion whenever n kills the actual kernel. -/
theorem cartierToPicard_pow (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) ^ n = 1 :=
  parameterCharacterDualPoint_pow f D n C.dual.X (C.sectionEquiv C.dual.X (𝟙 C.dual.X))
    (Schemes.characterSection_pow_eq_one (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) n hn C.dual.X _)

/-- The actual character-descent morphism lifted to the scheme-theoretic n-torsion of the dual. -/
def cartierToPicardTorsion (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    C.dual.X ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.abelian n :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  TorsionQuotient.SubgroupFunctor.torsionLift n (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) (cartierToPicard_pow f D n hn C)

/-- Inclusion of the torsion factor is exactly the morphism defined by actual character lines. -/
theorem cartierToPicardTorsion_inclusion (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    cartierToPicardTorsion f D n hn C ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n = ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  TorsionQuotient.SubgroupFunctor.torsionLift_ι n (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) (cartierToPicard_pow f D n hn C)

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTorsionFactor
