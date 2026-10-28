import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedLevelRelabeling

/-! # Two Level Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelExistence

noncomputable section

section

/-! Construct the bounded integral PEL parameter over the actual two-level
pure family. Every reduced integral PEL family admitting an auxiliary full
level has a geometric classifying map. Uniqueness and removal of the
auxiliary level are separate assertions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel.IntegralPureModel
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R)
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType L (Spec (.of R))) [NeZero N]
    [IsNoetherian M.space.left]

theorem exists_integral_two_level_pel_parameter (hM : M.IsFine)
    (hft : LocallyOfFiniteType M.space.hom) (hqc : QuasiCompact M.space.hom)
    (hsep : IsSeparated M.space.hom)
    (hN : ∀ x : M.space.left, IsUnit (N : M.space.left.presheaf.stalk x))
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.space.left, IsUnit (D.conductor : M.space.left.presheaf.stalk x)) :
    ∃ V : Over (Spec (.of R)), IsReduced V.left ∧ IsNoetherian V.left ∧
      LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
      ∃ U : PEL.Has.IntegralPELObject P R iotaO N V,
        Nonempty (U.data.polarized.abelian.FullLevel L) ∧
        ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
          (B : PEL.Has.IntegralPELObject P R iotaO N T),
          Nonempty (B.data.polarized.abelian.FullLevel L) →
          ∃ f : T ⟶ V, Nonempty (PEL.Iso.PolarizedActionIso (U.data.pullback f.left) B.data) := by
  let F := PureAddedLevel.IntegralPureModel.addedLevelSpace M hN (N := N)
  let A := (PureAddedLevel.IntegralPureModel.addedLevelUniversal M hN (N := N)).forgetAuxiliary
  let q := (PureAddedLevel.IntegralPureModel.prescribedFrame M hN (N := N)).hom
  have : IsFinite q := inferInstanceAs (IsFinite (PureAddedLevel.IntegralPureModel.addedLevelForget M hN (N := N)).left)
  have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace F.left := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian F.left := ⟨⟩
  have : LocallyOfFiniteType F.hom := by
    change LocallyOfFiniteType (q ≫ M.space.hom)
    infer_instance
  have : QuasiCompact F.hom := by
    change QuasiCompact (q ≫ M.space.hom)
    infer_instance
  have : IsSeparated F.hom := by
    change IsSeparated (q ≫ M.space.hom)
    infer_instance
  obtain ⟨Z, hr, hn, hZft, hZqc, hZsep, U, hU, hclass⟩ :=
    Relative.FamilyClassification.exists_bounded_relative_pel_universal_family P iotaO F A D hPresentations (fun x => by
      simpa only [map_natCast] using (hc (q x)).map (q.stalkMap x).hom)
  let V := (Over.map F.hom).obj Z
  have : IsReduced V.left := hr
  have : IsNoetherian V.left := hn
  have : LocallyOfFiniteType V.hom := by
    change LocallyOfFiniteType (Z.hom ≫ F.hom)
    infer_instance
  have : QuasiCompact V.hom := by
    change QuasiCompact (Z.hom ≫ F.hom)
    infer_instance
  have : IsSeparated V.hom := by
    change IsSeparated (Z.hom ≫ F.hom)
    infer_instance
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, U, ?_, ?_⟩
  · rw [hU]
    exact ⟨((PureAddedLevel.IntegralPureModel.addedLevelUniversal M hN (N := N)).auxiliary.level).pullback Z.hom⟩
  · rintro T _ B ⟨β⟩
    let B₂ : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel (3 * s) P.polarizationType L N T.left := {
      auxiliary := { B.data.polarized with level := β }
      prescribed := B.data.polarized.level }
    obtain ⟨f, ⟨e⟩⟩ := PureAddedLevel.IntegralPureModel.addedLevel_classifying_exists M hN hM T B₂
    let t : Over F.left := Over.mk f.left
    have : IsReduced t.left := inferInstanceAs (IsReduced T.left)
    let b : ((Over.map F.hom).obj t) ⟶ T := Over.homMk (𝟙 T.left) (by
      change 𝟙 T.left ≫ T.hom = f.left ≫ F.hom
      exact (Category.id_comp _).trans f.w.symm)
    let B' := B.pullback b
    let e' : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t.hom) B'.data.polarized :=
      e.forgetAuxiliary.trans (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId B.data.polarized).symm
    obtain ⟨j, ⟨ej⟩⟩ := hclass t B' ⟨e'⟩
    let k : T ⟶ V := Over.homMk j.left (by
      exact (Category.assoc j.left Z.hom F.hom).symm.trans
        ((congrArg (fun m => m ≫ F.hom) j.w).trans f.w))
    exact ⟨k, ⟨ej.trans (PEL.Iso.PolarizedActionIso.pullbackId B.data)⟩⟩

end

/-! The full pure HilbertConstruction graph input and bounded Presentations endomorphism-equation
input produce the actual integral two-level PEL parameter over a noetherian
coefficient ring. No pure model or PEL representation is supplied as input. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem integer_unit_at_stalk_of_base_unit {R : Type} [CommRing R]
    {S : Scheme.{0}} (p : S ⟶ Spec (.of R)) (n : ℕ) (hn : IsUnit (n : R)) (x : S) :
    IsUnit (n : S.presheaf.stalk x) := by
  let constants : R →+* Γ(S, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let toStalk : R →+* S.presheaf.stalk x :=
    (S.presheaf.germ ⊤ x (by trivial)).hom.comp constants
  simpa only [map_natCast] using hn.map toStalk

theorem exists_integral_bounded_two_level_pel_parameter
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [IsNoetherianRing R] {s L N : ℕ} [NeZero N]
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hs : 0 < s)
    (hδ : ∀ i, 0 < P.polarizationType i)
    (hchain : ∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j)
    (iotaO : NumberField.RingOfIntegers E →+* R)
    (hL : 3 ≤ L) (hcoprime : Nat.Coprime L (∏ i, P.polarizationType i))
    (hLunit : IsUnit (L : R)) (hNunit : IsUnit (N : R))
    (hδunit : ∀ i, IsUnit (P.polarizationType i : R))
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hc : IsUnit (D.conductor : R))
    (hHilbertConstruction : AbelianModuli.ReferenceFamily.Pure.Fine.PureHilbertConstructionInput) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ V : Over (Spec (.of R)), IsReduced V.left ∧ IsNoetherian V.left ∧
      LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
      ∃ U : PEL.Has.IntegralPELObject P R iotaO N V,
        Nonempty (U.data.polarized.abelian.FullLevel L) ∧
        ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
          (B : PEL.Has.IntegralPELObject P R iotaO N T),
          Nonempty (B.data.polarized.abelian.FullLevel L) →
          ∃ f : T ⟶ V, Nonempty (PEL.Iso.PolarizedActionIso (U.data.pullback f.left) B.data) := by
  obtain ⟨M, ⟨Q⟩, hM⟩ := hHilbertConstruction (3 * s) (by omega) P.polarizationType hδ hchain
    L hL hcoprime (Spec (.of R))
    (by simpa only [map_natCast] using hLunit.map (Scheme.ΓSpecIso (.of R)).inv.hom)
    (fun i => by simpa only [map_natCast] using
      (hδunit i).map (Scheme.ΓSpecIso (.of R)).inv.hom)
  have : LocallyOfFiniteType M.space.hom := Q.locallyFiniteType
  have : QuasiCompact M.space.hom := Q.quasiCompact
  have : IsLocallyNoetherian M.space.left := LocallyOfFiniteType.isLocallyNoetherian M.space.hom
  have : CompactSpace M.space.left := QuasiCompact.compactSpace_of_compactSpace M.space.hom
  have : IsNoetherian M.space.left := ⟨⟩
  exact exists_integral_two_level_pel_parameter P iotaO M hM Q.locallyFiniteType Q.quasiCompact
    Q.separated (integer_unit_at_stalk_of_base_unit M.space.hom N hNunit) D hPresentations
    (integer_unit_at_stalk_of_base_unit M.space.hom D.conductor hc)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelExistence
