import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardInjection

/-! # Cartier Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierInjection.Construction

noncomputable section

/-!
Geometric points detect the actual relative character-line map over an
arbitrary base. Fppf sheafification changes no sections at Spec of an
algebraically closed field, with any map from that field to the base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem fppf_over_geometric_sieve_eq_top
    {S : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (a : Spec (.of k) ⟶ S) (R : Sieve (Over.mk a))
    (hR : R ∈ (Scheme.fppfTopology.over S) (Over.mk a)) : R = ⊤ := by
  apply (Sieve.overEquiv _).injective
  rw [map_top]
  exact Picard.Homomorphisms.GeometricSheafification.Construction.fppf_sieve_algClosed_eq_top k _
    ((GrothendieckTopology.mem_over_iff Scheme.fppfTopology R).mp hR)

theorem toSheafify_geometric_bijective
    {S : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (a : Spec (.of k) ⟶ S) (P : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    Function.Bijective ((toSheafify (Scheme.fppfTopology.over S) P).app (.op (Over.mk a))) := by
  let J := Scheme.fppfTopology.over S
  let t := toSheafify J P
  constructor
  · intro x y h
    apply (Presheaf.equalizerSieve_eq_top_iff (F := P) x y).mp
    exact fppf_over_geometric_sieve_eq_top a _ (Presheaf.equalizerSieve_mem J t x y h)
  · intro x
    have htop := fppf_over_geometric_sieve_eq_top a _ (Presheaf.imageSieve_mem J t x)
    have hmem : Presheaf.imageSieve t x (𝟙 (Over.mk a)) := by
      rw [htop]
      trivial
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy.trans (by simp)⟩

theorem cartierToPicard_injective_over_geometric_point
    {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    {k : Type u} [Field k] [IsAlgClosed k] (a : Spec (.of k) ⟶ S) :
    Function.Injective (fun x : Over.mk a ⟶ C.dual.X => x ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  let Q : Over S := Over.mk a
  let A' := (Over.pullback a).obj A
  have : Smooth A'.hom := inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd A.hom a))
  have : IsProper A'.hom := inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd A.hom a))
  have : GeometricallyConnected A'.hom :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd A.hom a))
  have : IsIso A'.hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso A'
  have hp : Function.Surjective ((Over.pullback Q.hom).obj A).hom.appTop :=
    (ConcreteCategory.bijective_of_isIso A'.hom.appTop).surjective
  intro x y hxy
  apply (C.sectionEquiv Q).injective
  apply CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.parameterLineClass_injective f Q hp
  apply (toSheafify_geometric_bijective a (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B)).injective
  have hpoints : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q (C.sectionEquiv Q x) D =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q (C.sectionEquiv Q y) D :=
    (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C Q x).symm.trans (hxy.trans (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C Q y))
  exact (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint_poincare f Q (C.sectionEquiv Q x) D).symm.trans
    ((congrArg (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D) hpoints).trans
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint_poincare f Q (C.sectionEquiv Q y) D))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierInjection.Construction
