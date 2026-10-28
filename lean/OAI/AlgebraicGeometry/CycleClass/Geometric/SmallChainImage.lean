import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSmallness
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-! # Small Chain Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles

noncomputable section

/-!
# The actual image of small singular chains

The inclusion of the small singular simplicial set induces a genuine chain
map. In the canonical finite-support coefficient descriptions, it is precisely
extension along the inclusion of simplex indices. Hence its degreewise image
is exactly the chains whose support consists of small simplices.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

/-- Canonical simplex coefficients for the integral chains of any simplicial set. -/
def simplicialIntegralChainDegreeFinsuppIso (S : SSet.{0}) (n : ℕ) :
    (S.chainComplex (ModuleCat.of ℤ ℤ)).X n ≅
      ModuleCat.of ℤ (S.obj (.op ⦋n⦌) →₀ ℤ) :=
  (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (S.obj (.op ⦋n⦌)))

def simplicialIntegralChainCoefficients (S : SSet.{0}) (n : ℕ) :
    (S.chainComplex (ModuleCat.of ℤ ℤ)).X n ≃ₗ[ℤ] (S.obj (.op ⦋n⦌) →₀ ℤ) :=
  (simplicialIntegralChainDegreeFinsuppIso S n).toLinearEquiv

@[reassoc (attr := simp)]
theorem simplicialIntegralChainCoefficients_simplex (S : SSet.{0}) (n : ℕ)
    (s : S.obj (.op ⦋n⦌)) :
    S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
      (simplicialIntegralChainDegreeFinsuppIso S n).hom =
        ModuleCat.ofHom (Finsupp.lsingle s (R := ℤ) (M := ModuleCat.of ℤ ℤ)) :=
  (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (S.obj (.op ⦋n⦌))) (Discrete.mk s)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A simplicial map carries the coefficient of each source simplex to its
actual image simplex, adding coefficients if several images coincide. -/
theorem simplicialIntegralChainCoefficients_naturality {S T : SSet.{0}}
    (f : S ⟶ T) (n : ℕ) :
    (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n ≫
        (simplicialIntegralChainDegreeFinsuppIso T n).hom =
      (simplicialIntegralChainDegreeFinsuppIso S n).hom ≫
        ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (f.app (.op ⦋n⦌))) := by
  apply SSet.chainComplex_hom_ext
  intro s
  simp only [SSet.ι_chainComplexMap_f_assoc,
    simplicialIntegralChainCoefficients_simplex,
    simplicialIntegralChainCoefficients_simplex_assoc]
  apply ModuleCat.hom_ext
  ext a
  simp [Finsupp.lmapDomain_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise form of the genuine coefficient naturality identity. -/
theorem simplicialIntegralChainCoefficients_map {S T : SSet.{0}}
    (f : S ⟶ T) (n : ℕ) (c : (S.chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    simplicialIntegralChainCoefficients T n
        ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n c) =
      Finsupp.mapDomain (f.app (.op ⦋n⦌))
        (simplicialIntegralChainCoefficients S n c) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Finsupp.lmapDomain_apply] using!
    congrArg (fun g : (S.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ModuleCat.of ℤ (T.obj (.op ⦋n⦌) →₀ ℤ) => g.hom c)
      (simplicialIntegralChainCoefficients_naturality f n)

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Genuine integral chains of the small singular simplicial subcomplex. -/
abbrev integralSmallSingularChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)

/-- The actual chain map induced by inclusion of small singular simplices. -/
abbrev smallIntegralChainInclusion :
    integralSmallSingularChains X U ⟶ LocalHomology.Cycles.integralSingularChains X :=
  SSet.chainComplexMap (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)
    (ModuleCat.of ℤ ℤ)

/-- Canonical finite-support coefficients on the genuine small-chain complex. -/
abbrev smallIntegralChainCoefficients (n : ℕ) :
    (integralSmallSingularChains X U).X n ≃ₗ[ℤ]
      ((OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).obj (.op ⦋n⦌) →₀ ℤ) :=
  simplicialIntegralChainCoefficients
    (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) n

/-- In canonical coefficients the actual inclusion extends along the subtype
inclusion, with no arbitrary choice of a chain-level comparison map. -/
theorem smallIntegralChainInclusion_coefficients (n : ℕ)
    (c : (integralSmallSingularChains X U).X n) :
    SingularChainSupport.Cycles.singularChainCoefficients X n ((smallIntegralChainInclusion X U).f n c) =
      Finsupp.mapDomain Subtype.val (smallIntegralChainCoefficients X U n c) :=
  simplicialIntegralChainCoefficients_map
    (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U) n c

/-- The actual small-chain inclusion is injective in each degree. -/
theorem smallIntegralChainInclusion_injective (n : ℕ) :
    Function.Injective ((smallIntegralChainInclusion X U).f n) := by
  intro a b h
  apply (smallIntegralChainCoefficients X U n).injective
  apply Finsupp.mapDomain_injective Subtype.val_injective
  rw [← smallIntegralChainInclusion_coefficients, ← smallIntegralChainInclusion_coefficients, h]

instance smallIntegralChainInclusion_degree_mono (n : ℕ) :
    Mono ((smallIntegralChainInclusion X U).f n) :=
  (ModuleCat.mono_iff_injective _).mpr (smallIntegralChainInclusion_injective X U n)

instance smallIntegralChainInclusion_mono : Mono (smallIntegralChainInclusion X U) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

/-- The image of the genuine inclusion is exactly the chains supported on
small simplices. This identifies the support criterion with actual image membership. -/
theorem mem_range_smallIntegralChainInclusion_iff (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    c ∈ LinearMap.range ((smallIntegralChainInclusion X U).f n).hom ↔
      ∀ t ∈ SingularChainSupport.Cycles.singularChainSupport c,
        t ∈ (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌) := by
  constructor
  · rintro ⟨b, rfl⟩ t ht
    change t ∈ (SingularChainSupport.Cycles.singularChainCoefficients X n
      ((smallIntegralChainInclusion X U).f n b)).support at ht
    rw [smallIntegralChainInclusion_coefficients] at ht
    obtain ⟨s, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero
      (Finsupp.mem_support_iff.mp ht)
    exact s.property
  · intro hc
    have hcoeff : SingularChainSupport.Cycles.singularChainCoefficients X n c ∈ Set.range
        (Finsupp.mapDomain (Subtype.val :
          (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).obj (.op ⦋n⦌) →
            (TopCat.toSSet.obj X).obj (.op ⦋n⦌))) := by
      apply (Finsupp.mem_range_mapDomain_iff _ Subtype.val_injective _).2
      intro t ht
      by_contra hne
      apply ht
      exact ⟨⟨t, hc t (Finsupp.mem_support_iff.mpr hne)⟩, rfl⟩
    obtain ⟨b, hb⟩ := hcoeff
    refine ⟨(smallIntegralChainCoefficients X U n).symm b, ?_⟩
    apply (SingularChainSupport.Cycles.singularChainCoefficients X n).injective
    rw [smallIntegralChainInclusion_coefficients]
    exact (congrArg (Finsupp.mapDomain Subtype.val)
      ((smallIntegralChainCoefficients X U n).apply_symm_apply b)).trans hb

/-- The actual signed barycentric operator eventually lands in the actual
image of the small-chain inclusion for every finite integral chain. -/
theorem exists_subdivisionDegree_iterate_in_smallChainImage
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, (SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c ∈
      LinearMap.range ((smallIntegralChainInclusion X U).f n).hom := by
  obtain ⟨N, hN⟩ := SubdivisionSmallness.Cycles.exists_subdivisionDegree_iterate_small U hopen hcover c
  exact ⟨N, (mem_range_smallIntegralChainInclusion_iff X U n _).2 hN⟩

/-- Equivalent preimage formulation, with a genuine element of the small-chain complex. -/
theorem exists_subdivisionDegree_iterate_smallChain_preimage
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∃ b : (integralSmallSingularChains X U).X n,
      (smallIntegralChainInclusion X U).f n b = (SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c :=
  exists_subdivisionDegree_iterate_in_smallChainImage X U hopen hcover c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles
