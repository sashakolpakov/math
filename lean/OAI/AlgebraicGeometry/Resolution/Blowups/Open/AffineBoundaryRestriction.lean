import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback

/-! # Affine Boundary Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Native affine refinements transport full boundary and admissible-center atlases to open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (j : V ⟶ X)

def Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap (U : X.affineOpens) (W : V.affineOpens) (h : W.1 ≤ j ⁻¹ᵁ U.1) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) W
    Γ(X, U) →ₐ[ℂ] Γ(V, W) := by
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℂ Γ(V, W) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) W
  exact { toRingHom := (j.appLE U.1 W.1 h).hom
          commutes' := fun c => RingHom.congr_fun (Affine.ComplexNaturality.Construction.affineComplexScalars_appLE f j W U h) c }

theorem Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap_etale [IsOpenImmersion j]
    (U : X.affineOpens) (W : V.affineOpens) (h : W.1 ≤ j ⁻¹ᵁ U.1) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) W
    (Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap f j U W h).toRingHom.Etale := by
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℂ Γ(V, W) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) W
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  let φ := j.appLE U.1 W.1 h
  have he : Spec.map φ ≫ U.2.fromSpec = W.2.fromSpec ≫ j :=
    IsAffineOpen.SpecMap_appLE_fromSpec j U.2 W.2 h
  let : IsOpenImmersion (Spec.map φ ≫ U.2.fromSpec) := he.symm ▸ inferInstance
  let : IsOpenImmersion (Spec.map φ) := IsOpenImmersion.of_comp _ U.2.fromSpec
  exact (HasRingHomProperty.Spec_iff (P := @Etale) (φ := φ)).mp inferInstance

abbrev Open.AffineBoundaryRestriction.Construction.openAffineRefinement {ι : Type} (U : ι → X.affineOpens) : Type :=
  Σ i, {W : V.affineOpens // W.1 ≤ j ⁻¹ᵁ (U i).1}

theorem Open.AffineBoundaryRestriction.Construction.openAffineRefinement_cover {ι : Type} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i).1 = ⊤) :
    (⨆ r : Open.AffineBoundaryRestriction.Construction.openAffineRefinement j U, r.2.val.1) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  have hx : j x ∈ ⨆ i, (U i).1 := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := j ⁻¹ᵁ (U i).1) (x := x) hi
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨W, hW⟩, hsub⟩⟩, hxW⟩

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.comapOpen [IsOpenImmersion j]
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
      (Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap_etale f j _ _ _)
  · intro r
    let : Algebra ℂ Γ(X, A.opens r.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens r.1)
    let : Algebra ℂ Γ(V, r.2.val) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) r.2.val
    exact (A.faces r.1).map (φ r).toRingHom

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.comapOpen [IsOpenImmersion j]
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
      (Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap_etale f j _ _ _)
  · intro r
    let : Algebra ℂ Γ(X, A.opens r.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens r.1)
    let : Algebra ℂ Γ(V, r.2.val) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (j ≫ f) r.2.val
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I j (A.opens r.1) r.2.val r.2.property]
    exact (A.center r.1).etale_baseChange (S := .of Γ(V, r.2.val)) (φ r)
      (Open.AffineBoundaryRestriction.Construction.affineOpenSectionAlgMap_etale f j _ _ _)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
