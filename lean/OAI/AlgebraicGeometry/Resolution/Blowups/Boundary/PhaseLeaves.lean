import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ControlPhaseTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FamilyTransform

/-! # Phase Leaves -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary

noncomputable section

/-! Actual leaf maps, residual ideals, and individually retained old boundaries in a phase. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def PhaseLeaves.Construction.blowupChartConstantsAlgHom (k : Type u) {R : Type u}
    [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R) (a : I) : R →ₐ[k] Blowup.Charts.Construction.blowupChart I a where
  toRingHom := Blowup.Charts.Construction.blowupChartConstants I a
  commutes' _ := rfl

def ControlPhaseTree.Construction.BoundaryControlPhaseTree.Leaf {k : Type u} [CommRing k] {m : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J L : Ideal R}
    (T : ControlPhaseTree.Construction.BoundaryControlPhaseTree k m R J L) : Type u := by
  induction T with
  | terminal _ _ => exact ULift.{u} Unit
  | refineEtale hbound ι A f hf hcover children ih => exact Σ i, ih i
  | blowup hbound I hJ hL hfactor hsmooth hblowup ι g D hD hgen children ih => exact Σ i, ih i

instance ControlPhaseTree.Construction.BoundaryControlPhaseTree.leafFintype {k : Type u} [CommRing k] {m : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J L : Ideal R}
    (T : ControlPhaseTree.Construction.BoundaryControlPhaseTree k m R J L) : Fintype T.Leaf := by
  induction T with
  | terminal _ _ => exact inferInstanceAs (Fintype (ULift.{u} Unit))
  | refineEtale hbound ι A f hf hcover children ih =>
      let : ∀ i, Fintype (children i).Leaf := ih
      exact inferInstanceAs (Fintype (Σ i, (children i).Leaf))
  | blowup hbound I hJ hL hfactor hsmooth hblowup ι g D hD hgen children ih =>
      let : ∀ i, Fintype (children i).Leaf := ih
      exact inferInstanceAs (Fintype (Σ i, (children i).Leaf))

/-- A leaf retains the actual original-field map and every selected old
boundary equation. The same exceptional product accounts for control
`m` on the residual ideal and control one on each boundary equation. -/
structure PhaseLeaves.Construction.BoundaryPhaseLeafData (k : Type u) [CommRing k] (m : ℕ)
    (R : CommRingCat.{u}) [Algebra k R] (J : Ideal R) {ι : Type u} (w : ι → R) where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  exceptionalProduct : carrier
  residualIdeal : Ideal carrier
  boundary : ι → carrier
  residualFactorization : J.map map.toRingHom = Ideal.span {exceptionalProduct ^ m} * residualIdeal
  boundaryFactorization : ∀ i, map (w i) = exceptionalProduct * boundary i
  clearance : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k residualIdeal (m - 1) ⊔
    Ideal.span (Set.range boundary) = ⊤

attribute [instance] PhaseLeaves.Construction.BoundaryPhaseLeafData.algebra

/-- All leaf identities are computed from the actual phase and its
original boundary generators. Each individual old equation is divided
once at every blowup; it is never silently replaced by another family. -/
def ControlPhaseTree.Construction.BoundaryControlPhaseTree.leafData {k : Type u} [CommRing k] {m : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J L : Ideal R}
    (T : ControlPhaseTree.Construction.BoundaryControlPhaseTree k m R J L) {ι : Type u} :
    ∀ (w : ι → R), L = Ideal.span (Set.range w) → T.Leaf → PhaseLeaves.Construction.BoundaryPhaseLeafData k m R J w := by
  induction T with
  | @terminal R _ J L hbound hclear =>
      intro w hL _
      refine ⟨R, inferInstance, AlgHom.id k R, 1, J, w, ?_, ?_, ?_⟩
      · simp
      · intro i
        exact (one_mul (w i)).symm
      · exact hL ▸ hclear
  | @refineEtale R _ J L hbound κ _ A _ f hf hcover children ih =>
      intro w hL l
      obtain ⟨i, l⟩ := l
      let w' : ι → A i := fun j => f i (w j)
      have hL' : L.map (f i).toRingHom = Ideal.span (Set.range w') := by
        rw [hL, Ideal.map_span, ← Set.range_comp]
        rfl
      let C := ih i w' hL' l
      refine ⟨C.carrier, C.algebra, C.map.comp (f i), C.exceptionalProduct, C.residualIdeal, C.boundary,
        ?_, C.boundaryFactorization, C.clearance⟩
      change J.map (C.map.toRingHom.comp (f i).toRingHom) = _
      rw [← Ideal.map_map]
      exact C.residualFactorization
  | @blowup R _ J L hbound I hJ hLI hfactor hsmooth hblowup κ _ _ g D hD hgen children ih =>
      intro w hL l
      obtain ⟨i, l⟩ := l
      have hw (j : ι) : w j ∈ I := hLI (hL.symm ▸ Ideal.subset_span ⟨j, rfl⟩)
      let w' := FamilyTransform.Construction.blowupBoundaryFamily I (g i) w hw
      have hL' : ControlledTransform.Construction.blowupControlledTransform I L 1 (g i) = Ideal.span (Set.range w') := by
        rw [hL]
        exact FamilyTransform.Construction.blowupBoundaryFamily_controlledIdeal I (g i) w hw
      let C := ih i w' hL' l
      let c : C.carrier := C.map (Blowup.Charts.Construction.blowupChartConstants I (g i) (g i).val)
      refine ⟨C.carrier, C.algebra, C.map.comp (PhaseLeaves.Construction.blowupChartConstantsAlgHom k I (g i)),
        c * C.exceptionalProduct, C.residualIdeal, C.boundary, ?_, ?_, C.clearance⟩
      · change J.map (C.map.toRingHom.comp (Blowup.Charts.Construction.blowupChartConstants I (g i))) = _
        rw [← Ideal.map_map, ← ControlledTransform.Construction.blowup_controlledTransform_factorization I J m (g i) hJ,
          Ideal.map_mul, Ideal.map_span, Set.image_singleton, C.residualFactorization,
          ← mul_assoc, Ideal.span_singleton_mul_span_singleton]
        rw [map_pow C.map.toRingHom (Blowup.Charts.Construction.blowupChartConstants I (g i) (g i).val) m, mul_pow]
        rfl
      · intro j
        change C.map (Blowup.Charts.Construction.blowupChartConstants I (g i) (w j)) = (c * C.exceptionalProduct) * C.boundary j
        rw [FamilyTransform.Construction.blowupBoundaryFamily_factorization I (g i) w hw j, map_mul, C.boundaryFactorization j]
        exact (mul_assoc c C.exceptionalProduct (C.boundary j)).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary
