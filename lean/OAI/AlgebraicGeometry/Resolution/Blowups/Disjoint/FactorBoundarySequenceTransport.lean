import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorSequenceTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntegralIsoTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.RefinementAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundaryRefinement

/-! # Factor Boundary Sequence Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundarySequenceTransport.Construction

noncomputable section

/-! Replacing a disconnected center preserves integral-center continuations and every evolving boundary label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem disjointFactor_boundary_integral_sequence_transport
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (K L J : X.IdealSheafData)
    (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hJ : J ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    [Smooth (K.subschemeι ≫ f)] [Smooth (L.subschemeι ≫ f)]
    (b : ℕ) (hp : J ≤ (K * L) ^ b)
    (R : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL))
      (GlobalBlowup.Data.Construction.globalBlowupToBase (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (K * L) J (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) b))
    (hR : R.integralCenters) {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (K * L) D)
    (hRB : R.boundaryCompatible (Option β)
      (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) D)) :
    ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (FactorBlowupIso.Construction.disjointFactorBlowup K L hK hL)
      (GlobalBlowup.Data.Construction.globalBlowupToBase (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
        (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f))
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b) (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) b),
      S.integralCenters ∧ S.boundaryCompatible (Option (Option β)) (FactorBoundaryIdentity.Construction.disjointFactorBlowupBoundary K L hK hL D) := by
  let I := K * L
  have hI : I ≠ ⊥ := Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let κ := GlobalBlowup.Data.Construction.globalBlowupToBase K hK
  let L' := L.comap κ
  have hL' : L' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL
  let σ := GlobalBlowup.Data.Construction.globalBlowupToBase L' hL'
  let : Smooth (κ ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f K hK
  let : Smooth (L'.subschemeι ≫ (κ ≫ f)) := Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth f K L hK hdisjoint
  let : Smooth (σ ≫ (κ ≫ f)) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center (κ ≫ f) L' hL'
  let e := FactorControlledTransform.Construction.disjointFactorBlowupIso K L hK hL hdisjoint
  have he : e.hom ≫ π = σ ≫ κ := FactorControlledTransform.Construction.disjointFactorBlowupIso_over K L hK hL hdisjoint
  have hei : e.inv ≫ (σ ≫ κ) = π := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let J₂ := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal L' (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b) hL' b
  have hJ₂ : J₂ ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot L' _ hL' b
    (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot K J hK b hJ)
  have hg : e.inv ≫ (σ ≫ (κ ≫ f)) = π ≫ f := by
    rw [← Category.assoc σ κ f, ← Category.assoc, hei]
  have hJlocal : J₂.comap e.inv = GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b := by
    have h := congrArg (fun N => N.comap e.inv) (FactorControlledTransform.Construction.disjointFactorBlowupIso_controlled K L J hK hL hdisjoint b hp)
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id] at h
    exact h.symm
  let D₀ := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
  let Dold (l : Option β) := (D₀ l).comap e.hom
  have hDlocal : (fun l => (Dold l).comap e.inv) = D₀ := by
    funext l
    change ((D₀ l).comap e.hom).comap e.inv = D₀ l
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have hRB' : R.boundaryCompatible (Option β) (fun l => (Dold l).comap e.inv) := by
    rw [hDlocal]
    exact hRB
  have Aold : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (σ ≫ (κ ≫ f)) Dold [Finset.univ] := by
    have hA := (A.blowupBoundary hI).comapOpen (π ≫ f) e.hom
    change Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (e.hom ≫ (π ≫ f)) Dold [Finset.univ] at hA
    rw [← Category.assoc, he, Category.assoc] at hA
    exact hA
  obtain ⟨S, hS, hSB⟩ := R.transport_boundary_integral_iso hR (σ ≫ (κ ≫ f)) J₂ hJ₂
    e.symm hg hJlocal Dold Aold hRB'
  exact ⟨S, hS, S.boundaryCompatible_refine FactorBoundaryRefinement.Construction.mergeDisjointExceptionalLabels hSB
    (FactorBoundaryRefinement.Construction.disjointFactorBlowup_boundary_refinement K L hK hL hdisjoint D)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundarySequenceTransport.Construction
