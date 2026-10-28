import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing

/-! # Colon Disjoint Blowup Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ColonDisjointBlowupPullback.Construction

noncomputable section

/-! Ideal quotients commute with a blowup whose center is disjoint from the denominator ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem noetherianIdealSheafColon_comap_avoids_denominator
    {X Y : Scheme} [IsLocallyNoetherian X]
    (A K : X.IdealSheafData) (q : Y ⟶ X) (havoid : ∀ y : Y, q y ∉ K.support) :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A K).comap q = A.comap q := by
  let O : X.Opens := K.support.compl
  let : IsLocallyNoetherian O := LocallyOfFiniteType.isLocallyNoetherian O.ι
  let r := IsOpenImmersion.lift O.ι q (by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    exact havoid y)
  have hr : r ≫ O.ι = q := IsOpenImmersion.lift_fac O.ι q _
  have hbase : (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A K).comap O.ι = A.comap O.ι := by
    have hk : K.comap O.ι = ⊤ := Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top K
    rw [IdealSheaf.ColonRestriction.Construction.noetherianIdealSheafColon_comap_open, hk, GlobalControlled.Identities.Construction.noetherianIdealSheafColon_top_right]
  have h := congrArg (fun N => N.comap r) hbase
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hr] at h

theorem noetherianIdealSheafColon_comap_of_disjoint_isIso_complement
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (A K C : X.IdealSheafData) (π : Y ⟶ X) (hdisjoint : K ⊔ C = ⊤)
    [IsIso (π ∣_ C.support.compl)] :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A K).comap π =
      NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (A.comap π) (K.comap π) := by
  let O : Bool → X.Opens := fun b => if b then K.support.compl else C.support.compl
  let V (b : Bool) : Y.Opens := π ⁻¹ᵁ O b
  let E : Y.OpenCover := Scheme.Cover.mkOfCovers Bool (fun b => V b) (fun b => (V b).ι) (by
    intro y
    by_cases hy : π y ∈ K.support
    · have hc := Global.ResidualNeighborhood.Construction.idealSheaf_support_subset_complement_of_sup_top K C hdisjoint hy
      exact ⟨false, ⟨⟨y, hc⟩, rfl⟩⟩
    · exact ⟨true, ⟨⟨y, hy⟩, rfl⟩⟩) (fun _ => inferInstance)
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ E
  intro b
  change Bool at b
  let : IsLocallyNoetherian (V b) := LocallyOfFiniteType.isLocallyNoetherian (V b).ι
  change ((NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A K).comap π).comap (V b).ι =
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (A.comap π) (K.comap π)).comap (V b).ι
  rw [IdealSheaf.ColonRestriction.Construction.noetherianIdealSheafColon_comap_open (A.comap π) (K.comap π) (V b).ι,
    ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  cases b with
  | false =>
      let : IsIso (π ∣_ O false) := inferInstanceAs (IsIso (π ∣_ C.support.compl))
      have he : (π ∣_ O false) ≫ (O false).ι = (V false).ι ≫ π := morphismRestrict_ι π (O false)
      let : IsOpenImmersion ((V false).ι ≫ π) := by
        rw [← he]
        infer_instance
      exact IdealSheaf.ColonRestriction.Construction.noetherianIdealSheafColon_comap_open A K ((V false).ι ≫ π)
  | true =>
      have havoid : ∀ y : (V true), ((V true).ι ≫ π) y ∉ K.support := fun y => y.property
      rw [noetherianIdealSheafColon_comap_avoids_denominator A K _ havoid,
        ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support K _ havoid, GlobalControlled.Identities.Construction.noetherianIdealSheafColon_top_right]

theorem noetherianIdealSheafColon_comap_disjoint_blowup
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (A K C : X.IdealSheafData) (hC : C ≠ ⊥) (hdisjoint : K ⊔ C = ⊤) :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A K).comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC) =
      NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (A.comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC))
        (K.comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC)) := by
  let : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ∣_ C.support.compl) := Blowup.Complement.Construction.globalBlowup_supportComplement_isIso C hC
  exact noetherianIdealSheafColon_comap_of_disjoint_isIso_complement A K C
    (GlobalBlowup.Data.Construction.globalBlowupToBase C hC) hdisjoint

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ColonDisjointBlowupPullback.Construction
