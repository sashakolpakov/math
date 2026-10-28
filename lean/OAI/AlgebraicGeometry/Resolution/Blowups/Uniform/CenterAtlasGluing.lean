import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterSupportCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformIncidenceTransform

/-! # Center Atlas Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Pointed charts with one fixed incidence set glue to a native atlas with that set at every chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_ofPointedCharts
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (F : Finset β)
    (h : ∀ x : X, ∃ C : Global.MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart f I D, C.divided = F ∧
      ∃ p : PrimeSpectrum C.ring, C.map p = x) :
    ∃ A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ i, A.divided i = F := by
  choose C hF p hp using h
  let Q : X.AffineOpenCover := {
    I₀ := X
    X := fun x => (C x).ring
    f := fun x => (C x).map
    map_prop := fun x => (C x).isOpenImmersion
    idx := id
    covers := fun x => ⟨p x, hp x⟩ }
  let : ∀ x : Q.I₀, Algebra ℂ (Q.X x) := fun x => (C x).algebra
  let A := Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofAffineCover f I D Q (fun x => (C x).ground)
    (fun x => (C x).centerIdeal) (fun x => (C x).equations) (fun _ => F)
    (fun x => (C x).center_eq) (fun x => (C x).boundary_eq)
    (fun x => (C x).boundary) (fun x => hF x ▸ (C x).center)
  exact ⟨A, fun _ => rfl⟩

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_ofCenterCharts
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (F : Finset β)
    (h : ∀ x : X, x ∈ I.support → ∃ C : Global.MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart f I D, C.divided = F ∧
      ∃ p : PrimeSpectrum C.ring, C.map p = x) :
    ∃ B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ i, B.divided i = F := by
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_ofPointedCharts f I D F
  intro x
  by_cases hx : x ∈ I.support
  · exact h x hx
  · let O : X.Opens := I.support.compl
    let y : O := ⟨x, hx⟩
    let B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (O.ι ≫ f) (I.comap O.ι) (fun l => (D l).comap O.ι) := by
      rw [Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top]
      exact (A.comapOpen f O.ι).unitCenter
    have hB (i : B.indices) : (I.comap O.ι).ideal (B.opens i) = ⊤ := by
      exact congrArg (fun J : O.toScheme.IdealSheafData => J.ideal (B.opens i))
        (Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top I)
    let B' := B.withUniformIncidence F (fun i hp => (hp (hB i)).elim)
    obtain ⟨i, p, hp⟩ := Global.MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec B'.opens B'.cover y
    let C := (Global.MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofAtlas B' i).comp f I D O.ι
    refine ⟨C, rfl, p, ?_⟩
    change O.ι ((B'.opens i).2.fromSpec p) = x
    exact congrArg O.ι hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups
