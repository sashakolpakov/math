import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.AlgebraIsomorphismNeighborhood
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Affine Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.AffineIsomorphismNeighborhood

noncomputable section

/-! Actual affine scheme base-change projections that are isomorphisms
at a local spectrum extend to principal open neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

theorem affineAlgebra_baseChange_isIso_iff
    (B : Type u) [CommRing B] [Algebra R B] :
    IsIso (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ↔
        Function.Bijective (algebraMap B (B ⊗[R] A)) := by
  rw [← isIso_comp_left_iff (pullbackSpecIso R B A).inv,
    pullbackSpecIso_inv_fst', isIso_SpecMap_iff]
  rfl

theorem exists_principalOpen_affine_isomorphism [IsNoetherianRing R] [Module.Finite R A]
    (p : PrimeSpectrum R)
    (hp : IsIso (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    ∃ r ∉ p.asIdeal, IsIso (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := by
  obtain ⟨r, hr, h⟩ := AlgebraIsomorphismNeighborhood.exists_principalOpen_algebra_isomorphism (A := A) p
    ((affineAlgebra_baseChange_isIso_iff (R := R) (A := A) (Localization.AtPrime p.asIdeal)).mp hp)
  exact ⟨r, hr, (affineAlgebra_baseChange_isIso_iff (R := R) (A := A) (Localization.Away r)).mpr h⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.AffineIsomorphismNeighborhood
