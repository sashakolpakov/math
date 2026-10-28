import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas

/-! # Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual affine normal-crossing equations produce a native global full-boundary atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.ofAffineEquations
    (R : CommRingCat) [Algebra ℂ R] {β : Type} [Fintype β] (w : β → R)
    (B : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ R w) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)
      (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i})) [Finset.univ] := by
  let C : (Spec R).AffineOpenCover := {
    I₀ := PUnit
    X := fun _ => R
    f := fun _ => 𝟙 (Spec R)
    map_prop := fun _ => inferInstance
    idx := fun _ => PUnit.unit
    covers := fun x => ⟨x, rfl⟩ }
  let : ∀ i, Algebra ℂ (C.X i) := fun _ => inferInstanceAs (Algebra ℂ R)
  apply Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.ofAffineCover (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)
    (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i})) [Finset.univ] C
    (fun _ => Category.id_comp _) (fun _ => w)
  · intro i l
    exact Scheme.IdealSheafData.comap_id _
  · exact fun _ => B
  · exact fun _ => Boundary.Schedule.Construction.boundaryFacesCover_univ w

end

end OAI.AlgebraicGeometry.Resolution.Blowups
