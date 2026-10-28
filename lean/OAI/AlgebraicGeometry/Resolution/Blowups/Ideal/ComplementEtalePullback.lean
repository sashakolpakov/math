import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.AuxiliaryHistoryOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.TransformNaturality
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Complement Etale Pullback -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups

/-! Exact ideal pullback induces an actual étale pullback square on support complements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Ideal.ComplementEtalePullback.Construction.isPullback_resLE_of_eq {X Y : Scheme} (q : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (he : V = q ⁻¹ᵁ U) : IsPullback (q.resLE U V he.le) V.ι U.ι q := by
  subst V
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using isPullback_morphismRestrict q U

theorem Ideal.ComplementEtalePullback.Construction.exists_ideal_complement_etale_pullback {X Y : Scheme} (q : Y ⟶ X) [Etale q]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (hJ : I.comap q = J) :
    ∃ r : Scheme.Opens.toScheme (X := Y) J.support.compl ⟶ Scheme.Opens.toScheme (X := X) I.support.compl,
      Etale r ∧ IsPullback r (Scheme.Opens.ι (X := Y) J.support.compl) (Scheme.Opens.ι (X := X) I.support.compl) q := by
  have he : J.support.compl = q ⁻¹ᵁ I.support.compl := by
    ext y
    change y ∉ J.support ↔ q y ∉ I.support
    rw [← hJ, Scheme.IdealSheafData.support_comap]
    rfl
  let r := q.resLE I.support.compl J.support.compl he.le
  refine ⟨r, ?_, Ideal.ComplementEtalePullback.Construction.isPullback_resLE_of_eq q I.support.compl J.support.compl he⟩
  change Etale (Y.homOfLE he.le ≫ q ∣_ I.support.compl)
  infer_instance

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_transformed_boundary_complement_pullback
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData} (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M)
    (q : V ⟶ X) (r : W ⟶ Y) (hc : P.EtaleComparison Q q r)
    {β : Type} (D : β → X.IdealSheafData) (E : β → V.IdealSheafData)
    (hD : ∀ l, (D l).comap q = E l) (j : β) :
    ∃ s : (Q.transformedBoundaryComplement E j).toScheme ⟶ (P.transformedBoundaryComplement D j).toScheme,
      Etale s ∧ IsPullback s (Q.transformedBoundaryComplement E j).ι (P.transformedBoundaryComplement D j).ι r := by
  let : Etale r := (hc.endpoint_pullback P Q q r).1
  have he := hc.transformIdeal P Q q r (D j) 1
  rw [hD j] at he
  exact Ideal.ComplementEtalePullback.Construction.exists_ideal_complement_etale_pullback r (P.transformIdeal (D j) 1) (Q.transformIdeal (E j) 1) he

end AlgebraicGeometry.Resolution.Blowups

namespace AlgebraicGeometry.Resolution.Blowups.Ideal.ComplementEtalePullback.Construction

/-! A support covered by one map remains covered in the actual cartesian pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_support_cover_pullback
    {X Y U V : Scheme} (q : Y ⟶ X) (j : U ⟶ X) (j' : V ⟶ Y) (p : V ⟶ U)
    (hpb : IsPullback p j' j q) (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (hK : I.comap q = K) (hcover : (I.support : Set X) ⊆ Set.range j) :
    (K.support : Set Y) ⊆ Set.range j' := by
  intro y hy
  have hx : q y ∈ I.support := by
    rw [← hK, Scheme.IdealSheafData.support_comap] at hy
    exact hy
  obtain ⟨x, hx⟩ := hcover hx
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback hpb x y hx
  exact ⟨v, hv⟩

end AlgebraicGeometry.Resolution.Blowups.Ideal.ComplementEtalePullback.Construction

end

end OAI
