/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Sheaf.CohomologySection
import OAI.AlgebraicTopology.Sheaf.FlasqueLowerVanishing
import OAI.AlgebraicTopology.Sheaf.FlasqueCokernel

/-! # Flasque Lowest Cohomology -/

namespace OAI.AlgebraicTopology.Sheaf.FlasqueLowestCohomology.TopCat

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Lowest-degree cohomology comparison for flasque complexes

For a bounded-below termwise-flasque sheaf complex with cohomology sheaves zero below `n`,
the canonical map from cohomology of sections on any open `U` to sections of its degree-`n`
cohomology sheaf is an isomorphism, exhibited as the sheafification unit/counit comparison.
The proof shows the degree-`n` cohomology presheaf is already a sheaf, deriving flasqueness
of the preceding cycles from the lower vanishing and cokernel preservation from that.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

universe u

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an integer `n`, the kernel of the differential viewed as `K^{n-1} → Z^n(K)`
is canonically the preceding cycle sheaf `Z^{n-1}(K) = ker(d^{n-1})`. -/
def kernelBoundaryToCyclesIso (n : ℤ) :
    kernel (K.sc n).toCycles ≅ K.cycles ((ℤᵘᵖ).prev n) :=
  letI p := (ℤᵘᵖ).prev n
  letI hp : p = n - 1 := (ℤᵘᵖ).prev_eq' (ComplexShape.up_mk _ _ (by omega))
  letI hnext : (ℤᵘᵖ).next p = n :=
    (ℤᵘᵖ).next_eq' (ComplexShape.up_mk _ _ (by rw [hp]; omega))
  (kernelCompMono (K.sc n).toCycles (K.sc n).iCycles).symm ≪≫
    kernelIsoOfEq (K.sc n).toCycles_i ≪≫
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (K.sc n).f) (K.cyclesIsKernel p n hnext)

/-- In the first potentially nonzero cohomology degree, the forgetful functor
preserves the left homology of this short complex. -/
private theorem forget_preservesLeftHomologyOf_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    (forget AddCommGrpCat.{u} X).PreservesLeftHomologyOf (K.sc n) := by
  let F := forget AddCommGrpCat.{u} X
  let p := (ℤᵘᵖ).prev n
  have hp : p = n - 1 := (ℤᵘᵖ).prev_eq' (ComplexShape.up_mk _ _ (by omega))
  let : (K.cycles p).IsFlasque :=
    FlasqueLowerVanishing.TopCat.IsFlasque.BoundedBelowComplex.cycles_isFlasque_of_exact_le K N (n - 1)
      (fun j hj => (K.exactAt_iff_isZero_homology j).mpr (hK j (by omega)))
      hflasque p (by rw [hp])
  let : (F.obj (K.cycles ((ℤᵘᵖ).prev n))).IsFlasque :=
    inferInstanceAs ((K.cycles p).IsFlasque)
  let : (kernel (K.sc n).toCycles).IsFlasque :=
    FlasqueQuasiIso.TopCat.Presheaf.IsFlasque.of_iso (F.mapIso (kernelBoundaryToCyclesIso X K n))
  let : (K.sc n).X₁.IsFlasque := hflasque p
  let : (ShortComplex.LeftHomologyData.canonical (K.sc n)).IsPreservedBy F :=
    { g := inferInstance
      f' := FlasqueCokernel.TopCat.IsFlasque.forget_preservesCokernel (K.sc n).toCycles }
  exact Functor.PreservesLeftHomologyOf.mk' F (ShortComplex.LeftHomologyData.canonical (K.sc n))

/-- The lowest-degree section-cohomology presheaf is a sheaf. -/
private theorem sectionCohomologyPresheaf_isSheaf_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (CohomologyStalkVanishing.TopCat.sectionCohomologyPresheaf X K n) := by
  let := forget_preservesLeftHomologyOf_lowest X K N n hK hflasque
  let e : CohomologyStalkVanishing.TopCat.sectionCohomologyPresheaf X K n ≅ (K.homology n).obj :=
    (K.sc n).mapHomologyIso (forget AddCommGrpCat.{u} X)
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff e).mpr (K.homology n).property

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf-to-cohomology-sheaf comparison is an isomorphism, because
its sheafification unit is an isomorphism in this degree. -/
private theorem sectionCohomologyPresheafToSheaf_isIso_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    IsIso (CohomologySection.TopCat.sectionCohomologyPresheafToSheaf X K n) := by
  let := isIso_toSheafify (Opens.grothendieckTopology X)
    (sectionCohomologyPresheaf_isSheaf_lowest X K N n hK hflasque)
  dsimp only [CohomologySection.TopCat.sectionCohomologyPresheafToSheaf]
  infer_instance

/-- Lowest-degree cohomology of sections equals sections of the cohomology sheaf
on every open, via the already defined canonical comparison map. -/
theorem sectionCohomologyToSheafSection_isIso_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) : IsIso (CohomologySection.TopCat.sectionCohomologyToSheafSection X K n U) := by
  let := sectionCohomologyPresheafToSheaf_isIso_lowest X K N n hK hflasque
  dsimp only [CohomologySection.TopCat.sectionCohomologyToSheafSection]
  infer_instance

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. Assume `K` is zero below `N`, every term is flasque (all restriction maps are
surjective), and `𝓗^j(K) = 0` for `j < n`. For every open `U`, this isomorphism `H^n(K(U)) ≅
Γ(U, 𝓗^n(K))` sends a cocycle section to its class in the cohomology sheaf. -/
def lowestSectionCohomologyIso (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) :
    (((Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X U).mapHomologicalComplex ℤᵘᵖ).obj K).homology n ≅
      (K.homology n).presheaf.obj (op U) :=
  let := sectionCohomologyToSheafSection_isIso_lowest X K N n hK hflasque U
  asIso (CohomologySection.TopCat.sectionCohomologyToSheafSection X K n U)

end

end OAI.AlgebraicTopology.Sheaf.FlasqueLowestCohomology.TopCat
