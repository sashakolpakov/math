import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple

/-! # Relative Cohomology Excision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision

noncomputable section

/-!
# Rational relative cohomology excision for closed supports

The complement of a closed support and an open neighborhood of that support
form an actual open cover. Integral singular-chain excision for this cover,
together with the proved rational duality comparison, shows that restriction
of relative rational cochains is a quasi-isomorphism. Compactness and
separation assumptions are not needed.

All maps below are the existing pullbacks along continuous maps of pairs.
Naturality in the support and in its neighborhood holds already on cochains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple.Cohomology OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

/-- Actual restriction to a subspace, with the local support written as the
inverse image of the original support. The map exists for arbitrary sets;
the excision theorem below requires closed support and an open neighborhood. -/
abbrev closedSupportCochainRestriction (X : TopCat.{0}) (U K : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ :=
  AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportExcisionCochainMap X U K

@[reassoc (attr := simp)]
theorem closedSupportCochainRestriction_inclusion (X : TopCat.{0}) (U K : Set X) :
    closedSupportCochainRestriction X U K ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (LocalHomology.Cycles.subspaceInclusion X U) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportExcisionCochainMap_inclusion X U K

/-- Closed-support excision for the genuine relative rational cochains. -/
theorem closedSupportCochainRestriction_quasiIso (X : TopCat.{0}) (U K : Set X)
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    QuasiIso (closedSupportCochainRestriction X U K) := by
  have hcover : U ∪ Kᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  have : QuasiIso (LocalHomology.Cycles.relativeSingularChainsMap (LocalHomology.Cycles.subspaceInclusion X U)
      (show Set.MapsTo (LocalHomology.Cycles.subspaceInclusion X U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ Kᶜ from fun _ h => h)) :=
    LocalExcision.Cycles.relativeCoverInclusion_quasiIso X U Kᶜ hU hK.isOpen_compl hcover
  exact AlgebraicTopology.Duality.Poincare.CompactSupportExcision.relativeRationalCochainsMap_quasiIso_of_integral
    (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- Restriction on the existing relative rational cohomology groups. -/
abbrev closedSupportCohomologyRestriction (X : TopCat.{0}) (U K : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ n :=
  HomologicalComplex.homologyMap (closedSupportCochainRestriction X U K) n

/-- Actual relative-cohomology restriction is invertible for a closed support
contained in an open neighborhood. -/
theorem closedSupportCohomologyRestriction_isIso (X : TopCat.{0}) (U K : Set X)
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    IsIso (closedSupportCohomologyRestriction X U K n) := by
  have := closedSupportCochainRestriction_quasiIso X U K hK hU hKU
  infer_instance

/-- The canonical excision isomorphism for closed, possibly noncompact, supports. -/
def closedSupportCohomologyIso (X : TopCat.{0}) (U K : Set X)
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ n := by
  have := closedSupportCochainRestriction_quasiIso X U K hK hU hKU
  exact isoOfQuasiIsoAt (closedSupportCochainRestriction X U K) n

@[simp]
theorem closedSupportCohomologyIso_hom (X : TopCat.{0}) (U K : Set X)
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    (closedSupportCohomologyIso X U K hK hU hKU n).hom =
      closedSupportCohomologyRestriction X U K n := rfl

/-- The existing relative-kernel inclusion associated with enlarging a support. -/
abbrev supportCochainEnlargement (X : TopCat.{0}) {K L : Set X} (hKL : K ⊆ L) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ :=
  RelativeCochainTriple.Cohomology.relativeCochainTripleInclusion (ModuleCat.of ℚ ℚ) X Kᶜ Lᶜ
    (fun _ hx hK => hx (hKL hK))

@[reassoc (attr := simp)]
theorem supportCochainEnlargement_inclusion (X : TopCat.{0})
    {K L : Set X} (hKL : K ⊆ L) :
    supportCochainEnlargement X hKL ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ :=
  RelativeCochainTriple.Cohomology.relativeCochainTripleInclusion_inclusion (ModuleCat.of ℚ ℚ) X Kᶜ Lᶜ _

/-- Enlarging support on the existing relative cohomology. -/
abbrev supportCohomologyEnlargement (X : TopCat.{0}) {K L : Set X}
    (hKL : K ⊆ L) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Lᶜ n :=
  HomologicalComplex.homologyMap (supportCochainEnlargement X hKL) n

/-- Restriction and enlargement of support commute on actual cochains. -/
@[reassoc]
theorem closedSupportCochainRestriction_support_naturality (X : TopCat.{0})
    (U : Set X) {K L : Set X} (hKL : K ⊆ L) :
    supportCochainEnlargement X hKL ≫ closedSupportCochainRestriction X U L =
      closedSupportCochainRestriction X U K ≫
        supportCochainEnlargement (TopCat.of U) (Set.preimage_mono hKL) := by
  apply (cancel_mono (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
    ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' L)ᶜ)).mp
  erw [Category.assoc, closedSupportCochainRestriction_inclusion X U L,
    ← Category.assoc, supportCochainEnlargement_inclusion X hKL,
    Category.assoc, supportCochainEnlargement_inclusion (TopCat.of U)
      (show (LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K ⊆ (LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' L from
        Set.preimage_mono hKL), closedSupportCochainRestriction_inclusion X U K]

/-- Naturality of the closed-support excision isomorphism under support enlargement. -/
@[reassoc]
theorem closedSupportCohomologyIso_support_naturality (X : TopCat.{0})
    (U : Set X) {K L : Set X} (hK : IsClosed K) (hL : IsClosed L)
    (hU : IsOpen U) (hKL : K ⊆ L) (hLU : L ⊆ U) (n : ℕ) :
    supportCohomologyEnlargement X hKL n ≫
        (closedSupportCohomologyIso X U L hL hU hLU n).hom =
      (closedSupportCohomologyIso X U K hK hU (hKL.trans hLU) n).hom ≫
        supportCohomologyEnlargement (TopCat.of U) (Set.preimage_mono hKL) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    closedSupportCochainRestriction_support_naturality]

/-- Inverse excision has the same support naturality. -/
@[reassoc]
theorem closedSupportCohomologyIso_inv_support_naturality (X : TopCat.{0})
    (U : Set X) {K L : Set X} (hK : IsClosed K) (hL : IsClosed L)
    (hU : IsOpen U) (hKL : K ⊆ L) (hLU : L ⊆ U) (n : ℕ) :
    supportCohomologyEnlargement (TopCat.of U) (Set.preimage_mono hKL) n ≫
        (closedSupportCohomologyIso X U L hL hU hLU n).inv =
      (closedSupportCohomologyIso X U K hK hU (hKL.trans hLU) n).inv ≫
        supportCohomologyEnlargement X hKL n := by
  apply (cancel_mono (closedSupportCohomologyIso X U L hL hU hLU n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [closedSupportCohomologyIso_support_naturality X U hK hL hU hKL hLU n,
    Iso.inv_hom_id_assoc]

/-- Relative cochains restrict along the actual inclusion of two neighborhoods. -/
def supportNeighborhoodCochainRestriction (X : TopCat.{0})
    {U V : Set X} (hUV : U ⊆ V) (K : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of V)
        ((LocalHomology.Cycles.subspaceInclusion X V) ⁻¹' K)ᶜ ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (LocalHomology.Cycles.subspaceMap (𝟙 X) hUV)
    (fun _ hx => hx)

@[reassoc (attr := simp)]
theorem supportNeighborhoodCochainRestriction_inclusion (X : TopCat.{0})
    {U V : Set X} (hUV : U ⊆ V) (K : Set X) :
    supportNeighborhoodCochainRestriction X hUV K ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V)
          ((LocalHomology.Cycles.subspaceInclusion X V) ⁻¹' K)ᶜ ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (LocalHomology.Cycles.subspaceMap (𝟙 X) hUV) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) (LocalHomology.Cycles.subspaceMap (𝟙 X) hUV) _

/-- Restriction to a smaller neighborhood equals the two successive actual pullbacks. -/
@[reassoc]
theorem closedSupportCochainRestriction_open_naturality (X : TopCat.{0})
    {U V : Set X} (hUV : U ⊆ V) (K : Set X) :
    closedSupportCochainRestriction X V K ≫
        supportNeighborhoodCochainRestriction X hUV K =
      closedSupportCochainRestriction X U K := by
  apply (cancel_mono (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
    ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ)).mp
  rw [Category.assoc, supportNeighborhoodCochainRestriction_inclusion,
    ← Category.assoc, closedSupportCochainRestriction_inclusion,
    Category.assoc, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, LocalHomology.Cycles.subspaceMap_inclusion, Category.comp_id]
  exact (closedSupportCochainRestriction_inclusion X U K).symm

/-- The cohomology map induced by a smaller neighborhood inclusion. -/
abbrev supportNeighborhoodCohomologyRestriction (X : TopCat.{0})
    {U V : Set X} (hUV : U ⊆ V) (K : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V)
        ((LocalHomology.Cycles.subspaceInclusion X V) ⁻¹' K)ᶜ n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)ᶜ n :=
  HomologicalComplex.homologyMap (supportNeighborhoodCochainRestriction X hUV K) n

/-- The closed-support excision isomorphisms commute with actual open-neighborhood
restriction. Both neighborhoods contain the whole closed support. -/
@[reassoc]
theorem closedSupportCohomologyIso_open_naturality (X : TopCat.{0})
    {U V K : Set X} (hK : IsClosed K) (hU : IsOpen U) (hV : IsOpen V)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (n : ℕ) :
    (closedSupportCohomologyIso X V K hK hV (hKU.trans hUV) n).hom ≫
        supportNeighborhoodCohomologyRestriction X hUV K n =
      (closedSupportCohomologyIso X U K hK hU hKU n).hom := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, closedSupportCochainRestriction_open_naturality]

/-- Restricting between two open neighborhoods of the same closed support
is itself an isomorphism of the actual relative cohomology groups. -/
theorem supportNeighborhoodCohomologyRestriction_isIso (X : TopCat.{0})
    {U V K : Set X} (hK : IsClosed K) (hU : IsOpen U) (hV : IsOpen V)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (n : ℕ) :
    IsIso (supportNeighborhoodCohomologyRestriction X hUV K n) := by
  let e := closedSupportCohomologyIso X V K hK hV (hKU.trans hUV) n
  have : IsIso (e.hom ≫ supportNeighborhoodCohomologyRestriction X hUV K n) := by
    dsimp only [e]
    rw [closedSupportCohomologyIso_open_naturality X hK hU hV hKU hUV n]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom (supportNeighborhoodCohomologyRestriction X hUV K n)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision
