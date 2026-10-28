import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # Finite Fppf Cover -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFppfCover

noncomputable section

/-! A compact scheme's fppf covering sieve admits a finite affine
refinement. Its disjoint union is an actual fpqc covering morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

structure Family (Y : Scheme.{u}) (R : Sieve Y) where
  n : ℕ
  source : Fin n → Scheme.{u}
  map : ∀ i, source i ⟶ Y
  affine : ∀ i, IsAffine (source i)
  flat : ∀ i, Flat (map i)
  lfp : ∀ i, LocallyOfFinitePresentation (map i)
  covers : ∀ y : Y, ∃ i, ∃ x : source i, map i x = y
  member : ∀ i, R (map i)

attribute [instance] Family.affine Family.flat Family.lfp

variable {Y : Scheme.{u}} {R : Sieve Y}

theorem exists_finiteRefinement [CompactSpace Y] (hR : R ∈ Scheme.fppfTopology Y) :
    Nonempty (Family Y R) := by
  let P : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation
  have hP : P.IsStableUnderBaseChange :=
    { of_isPullback := fun sq hg ↦
        ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) sq hg.1,
          MorphismProperty.IsStableUnderBaseChange.of_isPullback
            (P := @LocallyOfFinitePresentation) sq hg.2⟩ }
  have hPm : P.IsMultiplicative :=
    { id_mem := fun _ ↦ ⟨inferInstance, inferInstance⟩
      comp_mem := fun f g hf hg ↦
        ⟨MorphismProperty.comp_mem (@Flat) f g hf.1 hg.1,
          MorphismProperty.comp_mem (@LocallyOfFinitePresentation) f g hf.2 hg.2⟩ }
  obtain ⟨𝒰, hmem⟩ := Scheme.exists_cover_of_mem_grothendieckTopology (P := P) hR
  have hflat (i : 𝒰.I₀) : Flat (𝒰.f i) := (𝒰.map_prop i).1
  have hlfp (i : 𝒰.I₀) : LocallyOfFinitePresentation (𝒰.f i) := (𝒰.map_prop i).2
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ (𝒰.f i).isOpenMap)
  obtain ⟨n, a, V, hV, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    𝒰.toPreZeroHypercover (U := ⊤) CompactSpace.isCompact_univ
  refine ⟨{
    n := n
    source := fun i ↦ (V i).toScheme
    map := fun i ↦ (V i).ι ≫ 𝒰.f (a i)
    affine := hV
    flat := fun i ↦ inferInstance
    lfp := fun i ↦ inferInstance
    covers := ?_
    member := ?_ }⟩
  · intro y
    have hy : y ∈ ⋃ i, 𝒰.f (a i) '' (V i) := by rw [hcov]; trivial
    obtain ⟨i, x, hx, hxy⟩ := Set.mem_iUnion.mp hy
    exact ⟨i, ⟨x, hx⟩, hxy⟩
  · intro i
    exact R.downward_closed (hmem _ _ (Presieve.ofArrows.mk (a i))) (V i).ι

def finiteRefinement [CompactSpace Y] (hR : R ∈ Scheme.fppfTopology Y) : Family Y R :=
  Classical.choice (exists_finiteRefinement hR)

variable (D : Family Y R)

def toCover : Scheme.Cover Scheme.fppfPrecoverage Y where
  I₀ := Fin D.n
  X := D.source
  f := D.map
  mem₀ := by
    rw [Scheme.fppfPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨D.covers, fun i ↦ ⟨D.flat i, D.lfp i⟩⟩

def total : Scheme.{u} := ∐ D.source

def projection : total D ⟶ Y := Sigma.desc D.map

instance total_affine : IsAffine (total D) := inferInstanceAs (IsAffine (∐ D.source))

instance projection_flat : Flat (projection D) :=
  inferInstanceAs (Flat (Sigma.desc D.map))

instance projection_surjective : Surjective (projection D) where
  surj y := by
    obtain ⟨i, x, hxy⟩ := D.covers y
    refine ⟨(Sigma.ι D.source i) x, ?_⟩
    exact (congrArg (fun a ↦ a x) (Sigma.ι_comp_desc D.map i)).trans hxy

instance projection_quasiCompact [QuasiSeparatedSpace Y] : QuasiCompact (projection D) := inferInstance

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFppfCover
