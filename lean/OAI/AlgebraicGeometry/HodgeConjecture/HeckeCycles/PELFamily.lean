import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # PEL Family -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Family

/-! The integral universal family of IntegralModel, expressed in TateComparison's actual
endomorphism and geometric Lie-signature conventions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

variable {R : Type} [CommRing R] {g N : ℕ} {S T : Scheme}

theorem action_ext {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    {a b : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A} (h : ∀ r, a.map r = b.map r) : a = b := by
  have hm : a.map = b.map := funext h
  cases a
  cases b
  cases hm
  rfl

theorem actionFromEnd_toEnd {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (a : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) : AbelianScheme.TateComparison.PELAdapters.actionFromEnd (AbelianScheme.TateComparison.PELAdapters.actionToEnd a) = a := by
  apply action_ext
  exact AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap a

theorem actionFromEnd_baseChange {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (a : R →+* AbelianScheme.TateComparison.End.IntegralEnd A.scheme) (f : T ⟶ S) :
    AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AbelianScheme.TateComparison.BaseChange.endBaseChange A.scheme f).comp a) =
      (AbelianScheme.TateComparison.PELAdapters.actionFromEnd a).pullback f := by
  apply action_ext
  intro r
  exact AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap A.scheme f (a r)

variable {E : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {δ : Fin g → ℕ}

def ofActionData (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S) :
    AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S :=
  AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized A.polarized (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action)

omit [NumberField E] [NumberField.IsCMField E] in
theorem ofActionData_pullback (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S) (f : T ⟶ S) :
    ofActionData (A.pullback f) = (ofActionData A).pullback f := by
  have ha : AbelianScheme.TateComparison.PELAdapters.actionToEnd (A.action.pullback f) =
      (AbelianScheme.TateComparison.BaseChange.endBaseChange A.polarized.abelian.scheme f).comp (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action) := by
    apply RingHom.ext
    intro r
    apply AbelianScheme.TateComparison.End.endSchemeMap_injective
    exact (AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap (A.action.pullback f) r).trans
      ((AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap A.polarized.abelian.scheme f (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action r)).trans
        (congrArg (fun z => (Over.pullback f).map z)
          (AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap A.action r))).symm
  change AbelianScheme.TateComparison.PEL.PELFamilyData.mk _ _ _ _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd (A.action.pullback f)) = _
  rw [ha]
  rfl

def baseAction (iotaO : NumberField.RingOfIntegers E →+* R) :
    NumberField.RingOfIntegers E →+* Γ(Spec (.of R), ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv.hom.comp iotaO

variable {iotaO : NumberField.RingOfIntegers E →+* R}
  {X : Over (Spec (.of R))}

omit [NumberField E] [NumberField.IsCMField E] in
theorem geometric_character {k : Type} [Field k] (j : R →+* k)
    (t : Spec (.of k) ⟶ X.left) (ht : t ≫ X.hom = Spec.map (CommRingCat.ofHom j)) :
    (Scheme.ΓSpecIso (.of k)).hom.hom.comp
      (t.appTop.hom.comp (X.hom.appTop.hom.comp (baseAction iotaO))) = j.comp iotaO := by
  have h : (Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop ≫ t.appTop ≫
      (Scheme.ΓSpecIso (.of k)).hom = CommRingCat.ofHom j := by
    rw [← Scheme.Hom.comp_appTop_assoc, ht, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f.hom.comp iotaO) h

omit [NumberField E] [NumberField.IsCMField E] in
theorem lie_fiber_iff (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S)
    {k : Type} [Field k] (t : Spec (.of k) ⟶ S)
    (χ : NumberField.RingOfIntegers E →+* k) (n : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank ((ofActionData A).abelian.pullback t)
      (AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AbelianScheme.TateComparison.BaseChange.endBaseChange (ofActionData A).abelian.scheme t).comp
        (ofActionData A).action)) χ n ↔
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.polarized.abelian.pullback t) (A.action.pullback t) χ n := by
  have ha := (actionFromEnd_baseChange (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action) t).trans
    (congrArg (fun a => a.pullback t) (actionFromEnd_toEnd A.action))
  exact iff_of_eq (congrArg (fun a =>
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.polarized.abelian.pullback t) a χ n) ha)

omit [NumberField.IsCMField E] in
theorem geometric_character_conjugate {k : Type} [Field k] (j : R →+* k)
    (t : Spec (.of k) ⟶ X.left) (ht : t ≫ X.hom = Spec.map (CommRingCat.ofHom j))
    (τ : E ≃ₐ[ℚ] E) :
    ((Scheme.ΓSpecIso (.of k)).hom.hom.comp
      (t.appTop.hom.comp (X.hom.appTop.hom.comp (baseAction iotaO)))).comp
      (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom =
        j.comp (iotaO.comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom)) := by
  exact congrArg (fun χ => χ.comp (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom)
    (geometric_character j t ht)

omit [NumberField.IsCMField E] in
/-- The two signatures use identical geometric fibers, dual-number points,
and O_E-characters. The different base-action conventions are identified. -/
theorem lie_signature_iff (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E (3 * s)
    P.polarizationType N X.left) :
    (ofActionData A).HasPrescribedLieSignature P
      (X.hom.appTop.hom.comp (baseAction iotaO)) ↔
      PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO X A.polarized.abelian A.action := by
  constructor
  · intro h k _ _ j t ht τ
    have h' := (lie_fiber_iff A t _ _).mp (h k t τ)
    exact (congrArg (fun χ => AbelianModuli.ReferenceFamily.LieRanks.HasLieRank
      (A.polarized.abelian.pullback t) (A.action.pullback t) χ (P.lieRank τ))
        (geometric_character_conjugate j t ht τ)).mp h'
  · intro h k _ _ t τ
    obtain ⟨j, hj⟩ := Spec.map_surjective (t ≫ X.hom)
    apply (lie_fiber_iff A t _ _).mpr
    exact (congrArg (fun χ => AbelianModuli.ReferenceFamily.LieRanks.HasLieRank
      (A.polarized.abelian.pullback t) (A.action.pullback t) χ (P.lieRank τ))
        (geometric_character_conjugate j.hom t hj.symm τ)).mpr (h k j.hom t hj.symm τ)

/-- The actual IntegralModel PEL object satisfies TateComparison's PEL locus, including
polarization type, positivity, Rosati, and every geometric Lie rank. -/
theorem integralObject_isPEL (A : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P R iotaO N X) :
    AbelianScheme.TateComparison.PELModuli.IsPELFamily P (X.hom.appTop.hom.comp (baseAction iotaO)) (ofActionData A.data) := by
  refine ⟨AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized_isPEL A.data.polarized (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.data.action)
    _ ((AbelianScheme.TateComparison.PELAdapters.rosati_iff A.data.polarized A.data.action).mpr A.rosati), ?_⟩
  exact (lie_signature_iff A.data).mpr A.lieRanks

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Family

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Isomorphisms

/-! Identify the actual PEL-family isomorphisms used by IntegralModel and TateComparison,
including their Poincare classes, ordered full levels, and ring actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Family

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {g N : ℕ} {δ : Fin g → ℕ} {S T Z : Scheme}
  {A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S}
  {B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N T} {f : Z ⟶ S} {h : Z ⟶ T}

def toFamilyIso (e : PELModuli.IntegralModel.PEL.Has.PulledBackPELDataIso A B f h) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((Family.ofActionData A).pullback f) ((Family.ofActionData B).pullback h) where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare :=
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.hom ⊗ₘ e.abelian.hom).left)
      (PELModuli.IntegralModel.PEL.BaseChange.poincareClass_pullback B h)).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e.dual.hom ⊗ₘ e.abelian.hom).left
        (AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap B.polarized.dual h)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.polarized.dual.poincare)).symm.trans
        (e.poincare.trans (PELModuli.IntegralModel.PEL.BaseChange.poincareClass_pullback A f).symm))
  equivariant r := by
    rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap, AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap]
    change (Over.pullback f).map (AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action r)) ≫ _ =
      _ ≫ (Over.pullback h).map (AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd B.action r))
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap, AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]
    exact e.action r
  marking := e.level

def fromFamilyIso
    (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((Family.ofActionData A).pullback f) ((Family.ofActionData B).pullback h)) :
    PELModuli.IntegralModel.PEL.Has.PulledBackPELDataIso A B f h where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare :=
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e.dual.hom ⊗ₘ e.abelian.hom).left
      (AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap B.polarized.dual h)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.polarized.dual.poincare)).trans
      ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.hom ⊗ₘ e.abelian.hom).left)
        (PELModuli.IntegralModel.PEL.BaseChange.poincareClass_pullback B h).symm).trans
        (e.poincare.trans (PELModuli.IntegralModel.PEL.BaseChange.poincareClass_pullback A f)))
  action r := by
    have he := e.equivariant r
    rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap, AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap] at he
    change (Over.pullback f).map (AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action r)) ≫ _ =
      _ ≫ (Over.pullback h).map (AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd B.action r)) at he
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap, AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap] at he
    exact he
  level := e.marking

/-- Identity base change, retaining every part of the PEL family. -/
def familyPullbackId (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((Family.ofActionData A).pullback (𝟙 S)) (Family.ofActionData A) where
  abelian := A.polarized.abelian.pullbackIdIso
  dual := A.polarized.dual.abelian.pullbackIdIso
  abelianGroup := A.polarized.abelian.pullbackIdIso_preservesGroup
  dualGroup := A.polarized.dual.abelian.pullbackIdIso_preservesGroup
  polarization := (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.polarized).polarization
  poincare := (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.polarized).poincare
  equivariant r := by
    rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap]
    change (Over.pullback (𝟙 S)).map (AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action r)) ≫
      A.polarized.abelian.pullbackIdIso.hom =
        A.polarized.abelian.pullbackIdIso.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action r)
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality (A.action.map r)
  marking := (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.polarized).level

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Isomorphisms

end

end OAI
