import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterMap
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! # Sheaf Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent.Construction

noncomputable section

/-!
# CartierDuality: affine tests determine fppf sheaves over an affine base

Affine open covers give cover density of the algebraic spectrum functor
on the big fppf site. No restriction on the test scheme is imposed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable (R : CommRingCat.{u})

instance e56AlgSpecCoverDense :
    (algSpec R).IsCoverDense (Scheme.fppfTopology.over (Spec R)) where
  is_cover X := by
    have hflat : MorphismProperty.IsStableUnderBaseChange (@Flat.{u}) := inferInstance
    have hfp : MorphismProperty.IsStableUnderBaseChange (@LocallyOfFinitePresentation.{u}) :=
      inferInstance
    have hfpMul : MorphismProperty.IsMultiplicative (@LocallyOfFinitePresentation.{u}) :=
      { id_mem := fun _ => inferInstance }
    let P : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation
    have hP : P.IsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.inf
    have hPMul : P.IsMultiplicative := MorphismProperty.IsMultiplicative.inf
    have hPIso : P.RespectsIso :=
      MorphismProperty.respectsIso_of_isStableUnderComposition
        (fun _ _ f hf => by
          let : IsIso f := hf
          exact ⟨inferInstance, inferInstance⟩)
    apply (Scheme.mem_overGrothendieckTopology
      (P := P) X _).mpr
    let 𝒰 : Scheme.Cover.{u}
        (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) X.left :=
      X.left.affineCover.changeProp (fun _ => ⟨inferInstance, inferInstance⟩)
    let (i : 𝒰.I₀) : (𝒰.X i).Over (Spec R) := ⟨𝒰.f i ≫ X.hom⟩
    let : 𝒰.Over (Spec R) := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰, inferInstance, ?_⟩
    rintro Y f ⟨i⟩
    have hAffine : IsAffine ((𝒰.X i).asOver (Spec R)).left := by
      change IsAffine (𝒰.X i)
      exact Scheme.isAffine_affineCover X.left i
    obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := R)
      (G := (𝒰.X i).asOver (Spec R))).mpr hAffine
    exact ⟨⟨A, e.inv, e.hom ≫ (𝒰.f i).asOver (Spec R),
      e.inv_hom_id_assoc _⟩⟩

/-- Maps of fppf sheaves over an affine base are determined, and can be
constructed, by their natural restrictions to all affine test schemes. -/
def affineSheafHomEquiv
    (F G : Sheaf (Scheme.fppfTopology.over (Spec R)) (Type (u + 1))) :
    (F ⟶ G) ≃ ((algSpec R).op ⋙ F.obj ⟶ (algSpec R).op ⋙ G.obj) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans
    (Functor.IsCoverDense.restrictHomEquivHom (G := algSpec R) (ℱ' := G)).symm

/-- A morphism of fppf sheaves over an affine base is an isomorphism
exactly when it is an isomorphism on every affine test scheme. -/
theorem sheafMap_isIso_iff_affine
    {F G : Sheaf (Scheme.fppfTopology.over (Spec R)) (Type (u + 1))} (f : F ⟶ G) :
    IsIso f ↔ ∀ A : (CommAlgCat R)ᵒᵖ,
      IsIso (f.hom.app (Opposite.op ((algSpec R).obj A))) := by
  constructor
  · intro hf A
    let : IsIso f := hf
    exact inferInstance
  · intro hf
    have h : IsIso (Functor.whiskerLeft (algSpec R).op f.hom) := by
      have (A : (CommAlgCat R)ᵒᵖᵒᵖ) :
          IsIso ((Functor.whiskerLeft (algSpec R).op f.hom).app A) := hf A.unop
      exact NatIso.isIso_of_isIso_app _
    exact Functor.IsCoverDense.iso_of_restrict_iso (G := algSpec R) f h

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent.Construction
