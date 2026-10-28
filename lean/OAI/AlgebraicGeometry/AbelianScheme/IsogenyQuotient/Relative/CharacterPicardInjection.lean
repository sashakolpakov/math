import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierInjection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterPicardValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KilledGroupEtale
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Character Picard Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CharacterPicardInjection.Construction

noncomputable section

/-! The character-line map itself is injective on all test schemes
when the original kernel has invertible exponent. No dual or other
representability assumption on the target Picard sheaf is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

theorem parameterCharacterPicardHom_geometric_injective
    {k : Type u} [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S) :
    Function.Injective (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f (Over.mk t)) := by
  let Q : Over S := Over.mk t
  let A' := (Over.pullback t).obj A
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd A.hom t))
  have : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : GeometricallyConnected A'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t))
  have : IsIso A'.hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso A'
  have hp : Function.Surjective ((Over.pullback Q.hom).obj A).hom.appTop :=
    (ConcreteCategory.bijective_of_isIso A'.hom.appTop).surjective
  intro χ ψ h
  apply CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.parameterLineClass_injective f Q hp
  apply (CartierInjection.Construction.toSheafify_geometric_bijective t (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B)).injective
  exact (Kernel.CharacterPicardValue.Construction.kernelCharacterPicardHom_relative_value f Q χ).symm.trans
    ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (.op Q)) h).trans
      (Kernel.CharacterPicardValue.Construction.kernelCharacterPicardHom_relative_value f Q ψ))

theorem parameterCharacterPicardHom_injective
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (T : Over S) : Function.Injective (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T) := by
  have : Etale C.dual.X.hom := KilledGroupEtale.Construction.cartierRepresentative_etale_of_killed (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) C n hn hk
  intro χ ψ h
  let x := (C.sectionEquiv T).symm χ
  let y := (C.sectionEquiv T).symm ψ
  have heq : x = y := by
    apply Geometric.Points.Construction.etale_ext_of_geometric_points
    intro k _ _ t a
    apply (C.sectionEquiv (Over.mk t)).injective
    apply parameterCharacterPicardHom_geometric_injective f t
    rw [C.sectionEquiv_natural, C.sectionEquiv_natural,
      show C.sectionEquiv T x = χ from (C.sectionEquiv T).apply_symm_apply χ,
      show C.sectionEquiv T y = ψ from (C.sectionEquiv T).apply_symm_apply ψ,
      ← CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterPicardHom_natural, ← CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterPicardHom_natural, h]
  exact ((C.sectionEquiv T).apply_symm_apply χ).symm.trans
    ((congrArg (C.sectionEquiv T) heq).trans ((C.sectionEquiv T).apply_symm_apply ψ))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CharacterPicardInjection.Construction
