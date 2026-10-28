import OAI.AlgebraicGeometry.SheafCohomology.Exact
import OAI.AlgebraicGeometry.SheafCohomology.Module
import OAI.AlgebraicGeometry.SheafCohomology.AffineCoverMono

/-! # Dimension Shift -/

namespace OAI.AlgebraicGeometry.SheafCohomology.DimensionShift.ProjectiveAffine

noncomputable section

/-!
# The injective step in affine dimension shifting

This file isolates the exact-sequence steps used in Kempf's affine-vanishing
argument. Given a short exact sequence of modules on a scheme, either
vanishing of degree `n` cohomology for the cokernel or surjectivity onto that
cohomology group makes the induced map on degree `n + 1` cohomology
injective. The proofs apply the actual connecting map in the long exact
sequence of the underlying abelian sheaves.

The second theorem is a checked downstream consumer for the genuine
affine-cover inclusion and cokernel constructed in
`SchemeModuleCohomologyAffineCoverMono`. It deliberately retains the
cokernel-cohomology hypothesis: proving that hypothesis from local killing is
the remaining mathematical part of affine vanishing.

The long exact sequence and exact forgetful functor are retained from
AINTLIB through the
attributed MazurTheorem port identified in this file's header.
-/

universe u

open _root_.CategoryTheory Limits _root_.TopologicalSpace
open _root_.AlgebraicGeometry

/-- In a short exact sequence, surjectivity of the second map on degree-`n`
cohomology makes the first map injective on degree `n + 1` cohomology. -/
theorem cohomology_succ_map_injective_of_previous_surjective
    {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ)
    (hsurjective : Function.Surjective
      ((AffineH.Projective.zariskiFunctor X n).map S.g)) :
    Function.Injective ((AffineH.Projective.zariskiFunctor X (n + 1)).map S.f) := by
  let Ssheaf := S.map (Module.ProjectiveAffine.ModuleSheaf.toSheaf X)
  have hSsheaf : Ssheaf.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS
      (Module.ProjectiveAffine.ModuleSheaf.toSheaf X)
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx⟩ := Exact.CategoryTheory.Sheaf.H.longSequence_exact₁_explicit
    hSsheaf n (n + 1) rfl c hc
  obtain ⟨y, hy⟩ := hsurjective x
  rw [← hx, ← hy]
  exact Exact.CategoryTheory.Sheaf.H.longSequence_comp_zero₃
    hSsheaf n (n + 1) rfl y

/-- In a short exact sequence, if degree-`n` cohomology of the cokernel is
subsingleton, then the first map is injective on degree `n + 1` cohomology. -/
theorem cohomology_succ_map_injective_of_cokernel_subsingleton
    {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (AffineH.Projective.H S.X₃ n)] :
    Function.Injective ((AffineH.Projective.zariskiFunctor X (n + 1)).map S.f) := by
  let Ssheaf := S.map (Module.ProjectiveAffine.ModuleSheaf.toSheaf X)
  have hSsheaf : Ssheaf.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS
      (Module.ProjectiveAffine.ModuleSheaf.toSheaf X)
  let : Subsingleton (CategoryTheory.Sheaf.H Ssheaf.X₃ n) := by
    change Subsingleton (AffineH.Projective.H S.X₃ n)
    infer_instance
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx⟩ := Exact.CategoryTheory.Sheaf.H.longSequence_exact₁_explicit
    hSsheaf n (n + 1) rfl c hc
  rw [← hx, Subsingleton.elim x 0, map_zero]
  rfl

/-- The affine-cover inclusion is injective on degree `n + 1` cohomology as
soon as degree-`n` cohomology of its actual cokernel vanishes. -/
theorem toAffineCoverModule_H_succ_injective_of_cokernel_subsingleton
    {R : CommRingCat.{u}} {I : Type u} (M : (Spec R).Modules)
    (U : I → (Spec R).Opens) (hU : IsOpenCover U) (n : ℕ)
    [Subsingleton (AffineH.Projective.H (cokernel (AffineCover.Projective.toAffineCoverModule M U)) n)] :
    Function.Injective
      ((AffineH.Projective.zariskiFunctor (Spec R) (n + 1)).map
        (AffineCover.Projective.toAffineCoverModule M U)) := by
  exact cohomology_succ_map_injective_of_cokernel_subsingleton
    (AffineCoverMono.Projective.affineCoverCokernel_shortExact M U hU) n

end

end OAI.AlgebraicGeometry.SheafCohomology.DimensionShift.ProjectiveAffine
