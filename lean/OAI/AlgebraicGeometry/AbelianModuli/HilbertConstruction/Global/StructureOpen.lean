import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.StructureRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.StructureRestriction

/-! # Structure Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The first-cohomology bound opens on affine charts give one actual
open of an arbitrary locally Noetherian base, with the same field criterion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (d : ℕ)

local instance Abelian.Schemes.AbelianScheme.affineChart_locallyNoetherian (i : S.affineCover.I₀) :
    IsLocallyNoetherian (S.affineCover.X i) :=
  LocallyOfFiniteType.isLocallyNoetherian (S.affineCover.f i)

def Abelian.Schemes.AbelianScheme.globalStructureH1Open : S.Opens :=
  ⨆ i, (S.affineCover.f i) ''ᵁ
    ((A.pullback (S.affineCover.f i)).structureH1Open (P.baseChange (S.affineCover.f i)) d)

theorem Abelian.Schemes.AbelianScheme.globalStructureH1Open_field_point
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S) :
    Set.range b ⊆ (A.globalStructureH1Open P d : Set S) ↔
      (A.pullback b).structureH1Dimension ≤ d := by
  constructor
  · intro hb
    let k₀ : Spec (.of K) := (⊥ : PrimeSpectrum K)
    have hx := hb (Set.mem_range_self k₀)
    obtain ⟨i, x, hx, he⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    let j := S.affineCover.f i
    have hr : Set.range b ⊆ Set.range j := by
      rintro _ ⟨k, rfl⟩
      exact ⟨x, he.trans (congrArg b (Subsingleton.elim k₀ k))⟩
    let c := IsOpenImmersion.lift j b hr
    have hc : c ≫ j = b := IsOpenImmersion.lift_fac j b hr
    have hcx (k : Spec (.of K)) : c k = x := by
      apply j.isOpenEmbedding.injective
      exact (congrArg (fun f : Spec (.of K) ⟶ S => f k) hc).trans
        ((congrArg b (Subsingleton.elim k k₀)).trans he.symm)
    have hcr : Set.range c ⊆ ((A.pullback j).structureH1Open (P.baseChange j) d : Set _) := by
      rintro _ ⟨k, rfl⟩
      exact hcx k ▸ hx
    have hdim := ((A.pullback j).structureH1Open_field_point (P.baseChange j) d c).mp hcr
    have hcomp := (A.pullback (c ≫ j)).structureH1Dimension_eq_of_iso
      ((A.pullback j).pullback c) (A.pullbackCompIso j c)
    rw [hc] at hcomp
    exact hcomp.le.trans hdim
  · intro hdim
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, x, hx⟩ := S.affineCover.exists_eq (b k)
    let j := S.affineCover.f i
    have hr : Set.range b ⊆ Set.range j := by
      rintro _ ⟨l, rfl⟩
      exact ⟨x, hx.trans (congrArg b (Subsingleton.elim k l))⟩
    let c := IsOpenImmersion.lift j b hr
    have hc : c ≫ j = b := IsOpenImmersion.lift_fac j b hr
    have hcomp := (A.pullback (c ≫ j)).structureH1Dimension_eq_of_iso
      ((A.pullback j).pullback c) (A.pullbackCompIso j c)
    rw [hc] at hcomp
    have hcr := ((A.pullback j).structureH1Open_field_point (P.baseChange j) d c).mpr
      (hcomp.symm.le.trans hdim)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨i, c k, hcr (Set.mem_range_self k), congrArg (fun f : Spec (.of K) ⟶ S => f k) hc⟩

theorem Abelian.Schemes.AbelianScheme.globalStructureH1Bound_of_range_subset
    {T : Scheme.{u}} (c : T ⟶ S)
    (hc : Set.range c ⊆ (A.globalStructureH1Open P d : Set S))
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ T) :
    ((A.pullback c).pullback b).structureH1Dimension ≤ d := by
  have hr : Set.range (b ≫ c) ⊆ (A.globalStructureH1Open P d : Set S) := by
    rintro _ ⟨k, rfl⟩
    exact hc (Set.mem_range_self (b k))
  have hdim := (A.globalStructureH1Open_field_point P d (b ≫ c)).mp hr
  exact (((A.pullback c).pullback b).structureH1Dimension_eq_of_iso
    (A.pullback (b ≫ c)) (A.pullbackCompIso c b).symm).le.trans hdim

theorem Abelian.Schemes.AbelianScheme.globalStructureH1Open_all_tests
    {T : Scheme.{u}} (c : T ⟶ S) :
    Set.range c ⊆ (A.globalStructureH1Open P d : Set S) ↔
      ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ T),
        ((A.pullback c).pullback b).structureH1Dimension ≤ d := by
  constructor
  · intro hc K _ b
    exact A.globalStructureH1Bound_of_range_subset P d c hc b
  · intro h
    rintro _ ⟨t, rfl⟩
    let b := T.fromSpecResidueField t
    have hdim := (((A.pullback c).pullback b).structureH1Dimension_eq_of_iso
      (A.pullback (b ≫ c)) (A.pullbackCompIso c b).symm).symm.le.trans (h _ b)
    have hr := (A.globalStructureH1Open_field_point P d (b ≫ c)).mpr hdim
    have hx := hr (Set.mem_range_self (⊥ : PrimeSpectrum (T.residueField t)))
    change c (T.fromSpecResidueField t (⊥ : PrimeSpectrum (T.residueField t))) ∈
      (A.globalStructureH1Open P d : Set S) at hx
    have he := T.fromSpecResidueField_apply t (⊥ : PrimeSpectrum (T.residueField t))
    exact (congrArg (fun x : T => c x ∈ (A.globalStructureH1Open P d : Set S)) he).mp hx

theorem Abelian.Schemes.AbelianScheme.globalStructureH1Open_bound
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ A.globalStructureH1Open P d) :
    ((A.pullback (A.globalStructureH1Open P d).ι).pullback b).structureH1Dimension ≤ d :=
  A.globalStructureH1Bound_of_range_subset P d (A.globalStructureH1Open P d).ι
    (by simp only [Scheme.Opens.range_ι, Set.Subset.refl]) b

theorem Abelian.Schemes.AbelianScheme.globalStructureH1Open_contains_polarized_fiber
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S)
    {N : ℕ} {δ : Fin g → ℕ}
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (e : (A.pullback b).scheme ≅ B.abelian.scheme)
    (hN : 3 ≤ N) (hNK : (N : K) ≠ 0) :
    Set.range b ⊆ (A.globalStructureH1Open P g : Set S) := by
  apply (A.globalStructureH1Open_field_point P g b).mpr
  exact ((A.pullback b).structureH1Dimension_eq_of_iso B.abelian e).le.trans
    (B.structureH1Dimension_eq hN hNK).le

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
