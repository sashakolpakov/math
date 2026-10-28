import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Center
import Mathlib.Topology.KrullDimension

/-! # Cover Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Dimension bounds are local on actual open affine covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Open.CoverDimension.Construction.topologicalKrullDim_le_of_open_cover
    {X : Type*} [TopologicalSpace X] {ι : Type*} (Y : ι → Type*) [∀ i, TopologicalSpace (Y i)]
    (j : ∀ i, Y i → X) (hj : ∀ i, Topology.IsOpenEmbedding (j i))
    (hc : ∀ x : X, ∃ i, ∃ y : Y i, j i y = x) (d : WithBot ℕ∞)
    (hd : ∀ i, topologicalKrullDim (Y i) ≤ d) : topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro Z
  obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
  obtain ⟨i, y, hy⟩ := hc x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (j i) (hj i)
  let V : {W : IrreducibleCloseds X | ((j i) ⁻¹' (W : Set X)).Nonempty} :=
    ⟨Z, ⟨y, by change j i y ∈ Z; rw [hy]; exact hx⟩⟩
  have he : IrreducibleCloseds.map (j i) (hj i).continuous (e.symm V) = Z :=
    congrArg Subtype.val (e.apply_symm_apply V)
  rw [← he, (hj i).coheight_map]
  exact (Order.coheight_le_krullDim (e.symm V)).trans (hd i)

theorem Open.CoverDimension.Construction.scheme_dimension_le_of_open_affine_cover
    {X : Scheme} {ι : Type*} (R : ι → CommRingCat) (j : ∀ i, Spec (R i) ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i, ∃ p : PrimeSpectrum (R i), j i p = x)
    (d : WithBot ℕ∞) (hd : ∀ i, ringKrullDim (R i) ≤ d) : topologicalKrullDim X ≤ d := by
  apply Open.CoverDimension.Construction.topologicalKrullDim_le_of_open_cover (fun i => PrimeSpectrum (R i))
    (fun i => j i) (fun i => (j i).isOpenEmbedding) hc d
  intro i
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact hd i

theorem Open.CoverDimension.Construction.ringKrullDim_le_of_affine_open_map
    {X : Scheme} (R : CommRingCat) (j : Spec R ⟶ X) [IsOpenImmersion j] :
    ringKrullDim R ≤ topologicalKrullDim X := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact j.isOpenEmbedding.isInducing.topologicalKrullDim_le

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.dimension_le
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (d : WithBot ℕ∞)
    (hd : ∀ i, ringKrullDim (A.rings i) ≤ d) : topologicalKrullDim X ≤ d := by
  apply Open.CoverDimension.Construction.scheme_dimension_le_of_open_affine_cover A.rings A.map ?_ d hd
  intro x
  have hx : x ∈ ⨆ i, (A.map i).opensRange := by rw [A.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.chart_dimension_le
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (d : WithBot ℕ∞) (hd : topologicalKrullDim X ≤ d) (i : A.indices) :
    ringKrullDim (A.rings i) ≤ d := (Open.CoverDimension.Construction.ringKrullDim_le_of_affine_open_map (A.rings i) (A.map i)).trans hd

end

end OAI.AlgebraicGeometry.Resolution.Blowups
