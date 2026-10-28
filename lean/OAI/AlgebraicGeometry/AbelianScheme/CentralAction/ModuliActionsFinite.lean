import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredSideFinite
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrderAlgebra

/-! # Moduli Actions Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ModuliActionsFinite.Construction

noncomputable section

/-! The actual graph automorphisms for T3 and C0 have finite order,
with the specified q-scalar clearing convention retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
  (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
  (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)

theorem centralModuliMap_eq_some_nat (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) :
    ∃ (aN : Fin s → ℕ) (hN : ℕ) (hNbound : ∀ v, aN v ≤ hN),
      PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags t a ha =
        Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison aN hN hNbound := by
  let aN : Fin s → ℕ := fun v => (a v).toNat
  let hN := t.val.multiplier.toNat
  have hnonneg (v : Fin s) : 0 ≤ a v := by
    rw [← ha v 0]
    exact (t.property.2 v 0).1
  have hab : ∀ v, aN v ≤ hN := by
    intro v
    apply Int.toNat_le_toNat
    rw [← ha v 0]
    exact (t.property.2 v 0).2
  have ht : t = Automorphisms.Construction.natCentralType aN hN hab := by
    apply Subtype.ext
    apply Automorphisms.Construction.localType_ext
    · exact (Int.toNat_of_nonneg t.property.1).symm
    · funext v i
      rw [ha v i]
      exact (Int.toNat_of_nonneg (hnonneg v)).symm
  have := PEL.Construction.central_correspondence_source_isIso D hgeometry hIsogenyQuotient hTateComparison.flags t a ha
  refine ⟨aN, hN, hab, ?_⟩
  apply (cancel_epi (D.correspondence t).source).mp
  rw [PEL.Construction.centralModuliMap_source, ht]
  exact (PEL.Construction.centralModuliMap_source D hgeometry hIsogenyQuotient hTateComparison.flags (Automorphisms.Construction.natCentralType aN hN hab)
    (fun v => aN v) (fun _ _ => rfl)).symm

theorem centralModuliAutomorphism_isOfFinOrder
    (hdegree : Module.finrank ℚ E = 2 * s) (hFiniteness : Arithmetic.Construction.PrincipalizationInput E)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ) (ha : ∀ v i, t.val.exponent v i = a v) :
    IsOfFinOrder (Automorphisms.Construction.centralModuliAutomorphism D hgeometry hgood hIsogenyQuotient A hTateComparison t a ha) := by
  apply FiniteOrderAlgebra.Construction.aut_finite_of_hom
  change IsOfFinOrder (End.of (PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags t a ha))
  obtain ⟨aN, hN, hbound, he⟩ := centralModuliMap_eq_some_nat D hgeometry hgood hIsogenyQuotient A hTateComparison t a ha
  rw [he]
  exact PoweredSideFinite.Construction.natCentralMap_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness aN hN hbound

theorem centralModuliAutomorphism_commute_shift
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ) (ha : ∀ v i, t.val.exponent v i = a v) :
    Commute (Automorphisms.Construction.centralModuliAutomorphism D hgeometry hgood hIsogenyQuotient A hTateComparison t a ha) A.markingShift := by
  apply Iso.ext
  change A.markingShift.hom ≫ PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags t a ha =
    PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags t a ha ≫ A.markingShift.hom
  obtain ⟨aN, hN, hbound, he⟩ := centralModuliMap_eq_some_nat D hgeometry hgood hIsogenyQuotient A hTateComparison t a ha
  rw [he, ← Automorphisms.Construction.natCentralMap_scalar D hgeometry hgood hIsogenyQuotient A hTateComparison]
  exact PoweredSideFinite.Construction.natCentralMap_commute D hgeometry hgood hIsogenyQuotient A hTateComparison aN (fun _ => 1) hN 2
    hbound (by intro; omega)

include hTateComparison in
theorem exists_finite_central_moduli_automorphisms
    (hdegree : Module.finrank ℚ E = 2 * s) (hFiniteness : Arithmetic.Construction.PrincipalizationInput E)
    (active : Fin s) (fullSide : Fin s → Bool) :
    ∃ (σT σC : Aut D.space),
      Interface.Construction.CorrespondenceIsGraph (D.correspondence (CentralRepresentatives.Construction.clearedT3Type active)) (σT ≪≫ A.markingShift) ∧
      Interface.Construction.CorrespondenceIsGraph (D.correspondence (CentralRepresentatives.Construction.c0IntegralType active fullSide)) σC ∧
      IsOfFinOrder σT ∧ IsOfFinOrder σC := by
  let eT := Automorphisms.Construction.centralModuliAutomorphism D hgeometry hgood hIsogenyQuotient A hTateComparison (CentralRepresentatives.Construction.clearedT3Type active)
    (fun v => CentralRepresentatives.Construction.t3Exponents active v + 1) (fun _ _ => rfl)
  let eC := Automorphisms.Construction.centralModuliAutomorphism D hgeometry hgood hIsogenyQuotient A hTateComparison (CentralRepresentatives.Construction.c0IntegralType active fullSide)
    (CentralRepresentatives.Construction.c0Exponents active fullSide) (fun _ _ => rfl)
  have hT : IsOfFinOrder eT := centralModuliAutomorphism_isOfFinOrder
    D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness _ _ _
  have hC : IsOfFinOrder eC := centralModuliAutomorphism_isOfFinOrder
    D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness _ _ _
  let shift : Aut D.space := A.markingShift
  have hS : IsOfFinOrder shift := by
    apply FiniteOrderAlgebra.Construction.aut_finite_of_hom
    change IsOfFinOrder (End.of A.markingShift.hom)
    rw [← Automorphisms.Construction.natCentralMap_scalar D hgeometry hgood hIsogenyQuotient A hTateComparison]
    exact PoweredSideFinite.Construction.natCentralMap_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness
      (fun _ => 1) 2 (by intro; omega)
  have hcomm : Commute eT A.markingShift :=
    centralModuliAutomorphism_commute_shift D hgeometry hgood hIsogenyQuotient A hTateComparison _ _ _
  refine ⟨eT ≪≫ A.markingShift.symm, eC, ?_, ?_, ?_, hC⟩
  · have he : (eT ≪≫ A.markingShift.symm) ≪≫ A.markingShift = eT := by
      apply Iso.ext
      change (eT.hom ≫ A.markingShift.inv) ≫ A.markingShift.hom = eT.hom
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he]
    exact Automorphisms.Construction.centralModuliAutomorphism_graph D hgeometry hgood hIsogenyQuotient A hTateComparison _ _ _
  · exact Automorphisms.Construction.centralModuliAutomorphism_graph D hgeometry hgood hIsogenyQuotient A hTateComparison _ _ _
  · exact hcomm.symm.inv_left.isOfFinOrder_mul hS.inv hT

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ModuliActionsFinite.Construction
