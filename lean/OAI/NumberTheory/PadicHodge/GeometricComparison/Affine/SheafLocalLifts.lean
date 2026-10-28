import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PrincipalRefinement
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Sheaf Local Lifts -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SheafLocalLifts.AffineSheafLocalLifts

noncomputable section

/-! Sections of the target of an actual epimorphism of affine module sheaves lift on a finite unit-ideal principal cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (A : CommRingCat.{u})

theorem exists_principal_lifts
    {F G : Sheaf (Opens.grothendieckTopology (Spec A)) (ModuleCat.{u} R)}
    (φ : F ⟶ G) [Epi φ] (x : G.obj.obj (op ⊤)) :
    ∃ t : Finset A, Ideal.span (t : Set A) = ⊤ ∧
      ∀ a : t, ∃ y : F.obj.obj (op (PrimeSpectrum.basicOpen a.val)),
        φ.hom.app _ y = G.obj.map (PrincipalRefinement.AffinePrincipalRefinement.principalArrow A a.val).op x := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} R) φ).mpr inferInstance
  obtain ⟨t, ht, hmem⟩ := PrincipalRefinement.AffinePrincipalRefinement.finite_refinement A
    (Presheaf.imageSieve φ.hom x)
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology (Spec A)) φ.hom x)
  exact ⟨t, ht, fun a => hmem a.val a.property⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SheafLocalLifts.AffineSheafLocalLifts
