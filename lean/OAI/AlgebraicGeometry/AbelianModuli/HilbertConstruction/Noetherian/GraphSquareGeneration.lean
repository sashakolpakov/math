import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.SquareFiniteMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.ResidueCohomology

/-! # Graph Square Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The graph-bundle square is globally generated on a Noetherian affine
tame base. Fiber sections lift using the proved vanishing of first cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_pointwise_sections_noetherian_affine
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∀ y : A.abelian.scheme.left,
      ∃ t : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf,
        y ∈ Ample.LineBundles.sectionNonvanishing t := by
  intro y
  let x := A.abelian.scheme.hom y
  let b := S.fromSpecResidueField x
  let B := A.pullback b
  let f := A.abelian.scheme.hom.fiberι x
  have hNk : (N : S.residueField x) ≠ 0 := by
    have hu := (Abelian.Schemes.level_unit_under_base_change b N hunit).map (Scheme.ΓSpecIso (S.residueField x)).hom.hom
    exact isUnit_iff_ne_zero.mp (by simpa only [map_natCast] using hu)
  have hgen : ∀ z : A.abelian.scheme.hom.fiber x,
      ∃ t : Line.Bundles.structureModule (A.abelian.scheme.hom.fiber x) ⟶
        ((A.graphBundle.tensorPower 2).pullback f).sheaf, z ∈ Ample.LineBundles.sectionNonvanishing t := by
    intro z
    obtain ⟨t, ht⟩ := B.graphBundle_square_pointwise_sections_overField hN hNk z
    let e : ((A.graphBundle.tensorPower 2).pullback f).sheaf ≅ (B.graphBundle.tensorPower 2).sheaf :=
      A.graphBundle.powerBaseChangeIso f 2 ≪≫
        (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left 2).mapIso (A.graphBundle_baseChangeIso b).symm
    exact ⟨t ≫ e.inv, (congrArg (fun U : B.abelian.scheme.left.Opens => z ∈ U)
      (Ample.Powers.sectionNonvanishing_comp_iso t e.symm)).mpr ht⟩
  have hr : y ∈ Set.range f := by
    rw [A.abelian.scheme.hom.range_fiberι x]
    rfl
  obtain ⟨z, hz⟩ := hr
  obtain ⟨t, ht⟩ := ProperFlat.FiberSectionGeneration.properFlat_global_sections_cover_fiber A.abelian.scheme.hom
    (A.graphBundle.tensorPower 2) x
    (A.graphBundle_residueFiber_positivePower_cohomology_subsingleton hN hunit x 2 (by decide) 0)
    hgen z
  exact ⟨t, hz ▸ ht⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_finite_section_cover_noetherian_affine
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∃ (n : ℕ) (s : Fin (n + 1) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf)),
      ∀ y : A.abelian.scheme.left, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  have : CompactSpace A.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  exact (A.graphBundle.tensorPower 2).finite_section_cover_of_pointwise
    (A.graphBundle_square_pointwise_sections_noetherian_affine hN hunit)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_finite_map_noetherian_affine
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∃ (n : ℕ) (s : Fin (n + 1) →
        (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf))
      (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)),
      IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left := by
  obtain ⟨n, s, hs⟩ := A.graphBundle_square_finite_section_cover_noetherian_affine hN hunit
  exact ⟨n, s, hs, A.graphBundle_square_sectionMap_isFinite s hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
