import OAI.AlgebraicGeometry.Resolution.Blowups.Open.AffineBoundaryRestriction

/-! # Boundary Atlas Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Native boundary and mixed-center atlases pull back along arbitrary étale morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (j : V ⟶ X)

theorem Etale.BoundaryAtlasPullback.Construction.affineSectionAlgMap_etale [Etale j]
    (U : X.affineOpens) (W : V.affineOpens) (h : W.1 ≤ j ⁻¹ᵁ U.1) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) W
    (Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap f j U W h).toRingHom.Etale := by
  exact j.etale_appLE U.2 W.2 h

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.comapEtale [Etale j]
    {β : Type} {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (j ≫ f) (fun l => (D l).comap j) L := by
  let φ (r : Open.AffineBoundaryRestriction.Construction.openAffineRefinement j A.opens) :=
    Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap f j (A.opens r.1) r.2.val r.2.property
  refine { indices := Open.AffineBoundaryRestriction.Construction.openAffineRefinement j A.opens
           opens := fun r => r.2.val
           cover := Open.AffineBoundaryRestriction.Construction.openAffineRefinement_cover j A.opens A.cover
           equations := fun r l => φ r (A.equations r.1 l)
           component := ?_
           boundary := ?_
           faces := ?_ }
  · intro r l
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le (D l) j (A.opens r.1) r.2.val r.2.property,
      A.component r.1 l, Ideal.map_span, Set.image_singleton]
    rfl
  · intro r
    let : Algebra ℂ Γ(X, A.opens r.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens r.1)
    let : Algebra ℂ Γ(V, r.2.val) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) r.2.val
    exact (A.boundary r.1).etale_baseChange (S := .of Γ(V, r.2.val)) (φ r)
      (Blowups.Etale.BoundaryAtlasPullback.Construction.affineSectionAlgMap_etale f j _ _ _)
  · intro r
    let : Algebra ℂ Γ(X, A.opens r.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens r.1)
    let : Algebra ℂ Γ(V, r.2.val) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) r.2.val
    exact (A.faces r.1).map (φ r).toRingHom

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.comapEtale [Etale j]
    {I : X.IdealSheafData} {β : Type} {D : β → X.IdealSheafData}
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j ≫ f) (I.comap j) (fun l => (D l).comap j) := by
  let φ (r : Open.AffineBoundaryRestriction.Construction.openAffineRefinement j A.opens) :=
    Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap f j (A.opens r.1) r.2.val r.2.property
  refine { indices := Open.AffineBoundaryRestriction.Construction.openAffineRefinement j A.opens
           opens := fun r => r.2.val
           cover := Open.AffineBoundaryRestriction.Construction.openAffineRefinement_cover j A.opens A.cover
           equations := fun r l => φ r (A.equations r.1 l)
           divided := fun r => A.divided r.1
           component := ?_
           contained := ?_
           boundary := ?_
           center := ?_ }
  · intro r l
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le (D l) j (A.opens r.1) r.2.val r.2.property,
      A.component r.1 l, Ideal.map_span, Set.image_singleton]
    rfl
  · intro r l hl
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I j (A.opens r.1) r.2.val r.2.property]
    exact Ideal.mem_map_of_mem _ (A.contained r.1 l hl)
  · intro r
    let : Algebra ℂ Γ(X, A.opens r.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens r.1)
    let : Algebra ℂ Γ(V, r.2.val) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) r.2.val
    exact (A.boundary r.1).etale_baseChange (S := .of Γ(V, r.2.val)) (φ r)
      (Blowups.Etale.BoundaryAtlasPullback.Construction.affineSectionAlgMap_etale f j _ _ _)
  · intro r
    let : Algebra ℂ Γ(X, A.opens r.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens r.1)
    let : Algebra ℂ Γ(V, r.2.val) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) r.2.val
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I j (A.opens r.1) r.2.val r.2.property]
    exact (A.center r.1).etale_baseChange (S := .of Γ(V, r.2.val)) (φ r)
      (Blowups.Etale.BoundaryAtlasPullback.Construction.affineSectionAlgMap_etale f j _ _ _)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
