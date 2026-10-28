import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Compatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierTorsionRepresentative
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism

/-! # Torsion Character Point -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionCharacterPoint

noncomputable section

/-! The actual Cartier character of a dual torsion point over any field is uniquely determined by its descended Poincare line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A) ^ n).left] [Flat ((𝟙 A) ^ n).left]
  [Surjective ((𝟙 A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A) ^ n).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

local instance normalizedHom : IsMonHom (show A ⟶ D.withPicardGroup.abelian from ell) :=
  PoincareBundle.Field.Compatibility.isMonHom D ell

local instance normalizedFinite : IsFinite (show A ⟶ D.withPicardGroup.abelian from ell).left :=
  inferInstanceAs (IsFinite ell.left)

local instance normalizedFlat : Flat (show A ⟶ D.withPicardGroup.abelian from ell).left :=
  inferInstanceAs (Flat ell.left)

local instance normalizedSurjective : Surjective (show A ⟶ D.withPicardGroup.abelian from ell).left :=
  inferInstanceAs (Surjective ell.left)

/-- Evaluate the inverse Cartier-Picard isomorphism at the prescribed dual point. -/
def character {T : Over (Spec (.of k))} (p : T ⟶ D.abelian) (hp : p ^ n = 1) :
    (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op T) := by
  have hpc : (show T ⟶ D.withPicardGroup.abelian from p) ^ n = 1 := by
    change (letI := Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D; p ^ n = 1)
    rw [PoincareBundle.Field.Compatibility.group_eq D]
    exact hp
  exact C.sectionEquiv T (CartierTorsionRepresentative.representative A D ell n hn C p hpc)

/-- The constructed character has precisely the required descended Poincare point. -/
theorem point {T : Over (Spec (.of k))} (p : T ⟶ D.abelian) (hp : p ^ n = 1) :
    AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A) ^ n) T (character A D ell n hn C p hp) D = p := by
  have hpc : (show T ⟶ D.withPicardGroup.abelian from p) ^ n = 1 := by
    change (letI := Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D; p ^ n = 1)
    rw [PoincareBundle.Field.Compatibility.group_eq D]
    exact hp
  have h := CartierTorsionRepresentative.representative_point A D ell n hn C p hpc
  exact h

/-- Actual character-line descent distinguishes full character sections, including infinitesimal tests. -/
theorem point_injective (T : Over (Spec (.of k))) :
    Function.Injective (fun χ => AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A) ^ n) T χ D) := by
  intro χ ψ h
  apply AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterPicardHom_injective ((𝟙 A) ^ n) T
  exact (D.representable.homEquiv.apply_symm_apply _).symm.trans
    ((congrArg D.representable.homEquiv h).trans (D.representable.homEquiv.apply_symm_apply _))

/-- A character with the prescribed Poincare point is the constructed one. -/
theorem unique {T : Over (Spec (.of k))} (p : T ⟶ D.abelian) (hp : p ^ n = 1)
    (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op T))
    (hχ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A) ^ n) T χ D = p) :
    χ = character A D ell n hn C p hp :=
  point_injective A D n T (hχ.trans (point A D ell n hn C p hp).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionCharacterPoint
