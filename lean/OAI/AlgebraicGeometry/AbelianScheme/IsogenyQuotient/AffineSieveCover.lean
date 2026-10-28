import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent

/-! # Affine Sieve Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffineSieveCover.Construction

/-! A sieve containing every arrow from an affine test scheme is fppf
covering, over an arbitrary base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem fppfSieve_mem_of_affine_arrows {S : Scheme.{u}} (T : Over S) (R : Sieve T)
    (h : ∀ (U : Over S) [IsAffine U.left] (f : U ⟶ T), R f) :
    R ∈ (Scheme.fppfTopology.over S) T := by
  have hfpMul : MorphismProperty.IsMultiplicative (@LocallyOfFinitePresentation.{u}) :=
    { id_mem := fun _ => inferInstance }
  let P : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation
  have hP : P.IsStableUnderBaseChange := MorphismProperty.IsStableUnderBaseChange.inf
  have hPMul : P.IsMultiplicative := MorphismProperty.IsMultiplicative.inf
  have hPIso : P.RespectsIso := MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f hf => by let : IsIso f := hf; exact ⟨inferInstance, inferInstance⟩)
  apply (Scheme.mem_overGrothendieckTopology (P := P) T R).mpr
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage P) T.left :=
    T.left.affineCover.changeProp (fun _ => ⟨inferInstance, inferInstance⟩)
  let (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ T.hom⟩
  let : 𝒰.Over S := { isOver_map _ := ⟨rfl⟩ }
  refine ⟨𝒰, inferInstance, ?_⟩
  rintro U f ⟨i⟩
  have : IsAffine ((𝒰.X i).asOver S).left := Scheme.isAffine_affineCover T.left i
  exact h _ ((𝒰.f i).asOver S)

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffineSieveCover.Construction
