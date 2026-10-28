import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredDualQuotients
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.QuotientPoincareDescent

/-! # Powered Side Finite -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.CentralAction.PoweredSideFinite

/-! The powered scalar quotient is an isomorphism of the complete PEL
family, including the raw Poincare bundle and full finite marking. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem fiber_scalar_quotient_poincare
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (β : 𝓞 E) (n : ℕ) (hn : n ≠ 0)
    (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = n)
    (hmark : Marking.Construction.levelReduction E D.level β = 1)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x y : D.GeometricPoint b)
    (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) n)
    (j : (D.fiberFamily b y).abelian.scheme ≅ (D.fiberFamily b x).abelian.scheme)
    [IsMonHom j.hom] (hj : f.isogeny.hom ≫ j.hom = Scalar.Construction.scalarMap (D.fiberFamily b x) β) :
    QuotientPoincareDescent.Construction.QuotientPoincareCompatible (D.fiberFamily b x) (D.fiberFamily b y) j := by
  let g := PoweredQuotients.Construction.fiberScalarIsogeny D hgeometry β n hn hnorm hmark b x
  have hd := PoweredDualQuotients.Construction.fiber_scalar_quotient_dual_polarization D hgeometry β n hn hnorm hmark b x y f j hj
  have hpol := (GenericModuli.Construction.generic_family_polarizationType D hgeometry).pullback x.left
  have hf : Etale f.isogeny.hom.left := PolarizationEtale.Construction.pelIsogeny_etale_of_polarization_type f
    D.reference.polarizationType hpol (ScalarIsogeny.Construction.nat_unit_on_charZero_scheme b n hn)
  have hfac : f.isogeny.hom ≫ j.hom = g.isogeny.hom :=
    hj.trans (PoweredQuotients.Construction.fiberScalarIsogeny_hom D hgeometry β n hn hnorm hmark b x).symm
  exact QuotientPoincareDescent.Construction.quotient_poincare_descent f g j hfac hd

theorem exists_powered_side_pel_isomorphisms
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
    (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
    (hFiniteness : Arithmetic.Construction.PrincipalizationInput E) (side : Fin s → Bool) :
    ∃ n : ℕ, 0 < n ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
        (x : D.GeometricPoint b),
        ∃ y : D.GeometricPoint b,
          y = x ≫ Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison
            (PoweredKernels.Construction.sideChosenExponent side) 1 (PoweredKernels.Construction.sideChosenExponent_le_one side) ^ n ∧
          Nonempty (TateComparison.PELModuli.PELFamilyIso (D.fiberFamily b y) (D.fiberFamily b x)) := by
  obtain ⟨n, β, hn, _, hnorm, hmark, hh⟩ :=
    PoweredQuotients.Construction.exists_powered_side_scalar_quotients D hgeometry hgood hdegree hIsogenyQuotient A hTateComparison hFiniteness side
  refine ⟨n, hn, ?_⟩
  intro k _ _ b x
  obtain ⟨y, f, j, hy, hj, hfac, hact, hlevel⟩ := hh k b x
  have hnq : q ^ n ≠ 0 := pow_ne_zero _ (Fact.out : q.Prime).ne_zero
  have hnorm' : β * IsCMField.ringOfIntegersComplexConj E β = (q ^ n : ℕ) := by
    simpa only [Nat.cast_pow] using hnorm
  have hd := PoweredDualQuotients.Construction.fiber_scalar_quotient_dual_polarization D hgeometry β (q ^ n) hnq
    hnorm' hmark b x y f j hfac
  have hp := fiber_scalar_quotient_poincare D hgeometry β (q ^ n) hnq hnorm' hmark b x y f j hfac
  refine ⟨y, hy, ⟨{
    abelian := j
    dual := (DualPicard.Construction.dualUnderlyingIso (D.fiberFamily b y).dual (D.fiberFamily b x).dual j).symm
    abelianGroup := hj
    dualGroup := hd.1
    polarization := hd.2
    poincare := hp
    equivariant := hact
    marking := hlevel }⟩⟩

end Construction

end AlgebraicGeometry.AbelianScheme.CentralAction.PoweredSideFinite

namespace AlgebraicGeometry.AbelianScheme.CentralAction.PoweredSideFinite.Construction
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NumberField
section

/-! A uniform principal scalar power fixes the complete fine moduli
scheme, including every component, by the proved full PEL isomorphisms. -/

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem exists_powered_side_identity
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
    (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
    (hFiniteness : Arithmetic.Construction.PrincipalizationInput E) (side : Fin s → Bool) :
    ∃ n : ℕ, 0 < n ∧
      Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison
        (PoweredKernels.Construction.sideChosenExponent side) 1 (PoweredKernels.Construction.sideChosenExponent_le_one side) ^ n = 1 := by
  obtain ⟨n, hn, hh⟩ :=
    exists_powered_side_pel_isomorphisms D hgeometry hgood hdegree hIsogenyQuotient A hTateComparison hFiniteness side
  refine ⟨n, hn, ?_⟩
  have : Smooth D.model.space.hom := hgeometry.smooth
  have : IsProper D.model.space.hom := hgeometry.proper
  have : Smooth D.space.hom := inferInstanceAs
    (Smooth (pullback.snd D.model.space.hom D.generic))
  have : IsProper D.space.hom := inferInstanceAs
    (IsProper (pullback.snd D.model.space.hom D.generic))
  have : IsReduced D.space.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.space.hom
  apply TateComparison.GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  have : IsReduced (Over.mk b).left := inferInstanceAs (IsReduced (Spec (.of k)))
  obtain ⟨y, hy, ⟨e⟩⟩ := hh k b x
  have hxy : y = x := GenericModuli.Construction.generic_classifying_maps_eq_of_pelIso D hgeometry y x e
  exact hy.symm.trans (hxy.trans (Category.comp_id x).symm)

end

/-! All integral central moduli maps are commuting products of the
selected-side maps, so they have finite order on the whole moduli scheme. -/

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
  (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
  (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)

theorem natCentralMap_commute (a b : Fin s → ℕ) (h k : ℕ)
    (ha : ∀ v, a v ≤ h) (hb : ∀ v, b v ≤ k) :
    Commute (Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha)
      (Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison b k hb) := by
  change _ ≫ _ = _ ≫ _
  rw [Automorphisms.Construction.natCentralMap_comp, Automorphisms.Construction.natCentralMap_comp]
  simp only [Nat.add_comm]

theorem natCentralMap_isOfFinOrder
    (hdegree : Module.finrank ℚ E = 2 * s) (hFiniteness : Arithmetic.Construction.PrincipalizationInput E)
    (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h) :
    IsOfFinOrder (Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha) := by
  classical
  induction h generalizing a with
  | zero =>
    have hzero : a = fun _ => 0 := funext (fun v => Nat.eq_zero_of_le_zero (ha v))
    subst a
    rw [Automorphisms.Construction.natCentralMap_zero]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.one_pos, one_pow 1⟩
  | succ h ih =>
    let side : Fin s → Bool := fun v => decide (a v = 0)
    let b := PoweredKernels.Construction.sideChosenExponent side
    let c : Fin s → ℕ := fun v => a v - b v
    have hb (v : Fin s) : b v ≤ a v := by
      by_cases hz : a v = 0
      · simp [b, side, PoweredKernels.Construction.sideChosenExponent, hz]
      · simp only [b, side, PoweredKernels.Construction.sideChosenExponent, decide_eq_false hz, Bool.false_eq_true,
          ↓reduceIte]
        omega
    have hc (v : Fin s) : c v ≤ h := by
      have hav := ha v
      by_cases hz : a v = 0
      · simp [c, hz]
      · simp only [c, b, side, PoweredKernels.Construction.sideChosenExponent, decide_eq_false hz, Bool.false_eq_true,
          ↓reduceIte]
        omega
    have hbf : IsOfFinOrder (Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison b 1
        (PoweredKernels.Construction.sideChosenExponent_le_one side)) :=
      isOfFinOrder_iff_pow_eq_one.mpr
        (exists_powered_side_identity D hgeometry hgood hdegree hIsogenyQuotient A hTateComparison hFiniteness side)
    have hcf := ih c hc
    have hf := (natCentralMap_commute D hgeometry hgood hIsogenyQuotient A hTateComparison b c 1 h
      (PoweredKernels.Construction.sideChosenExponent_le_one side) hc).isOfFinOrder_mul hbf hcf
    change IsOfFinOrder (End.of (Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison c h hc ≫
      Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison b 1 (PoweredKernels.Construction.sideChosenExponent_le_one side))) at hf
    rw [Automorphisms.Construction.natCentralMap_comp] at hf
    have hsum : (fun v => c v + b v) = a := funext (fun v => Nat.sub_add_cancel (hb v))
    simpa only [hsum] using hf

end AlgebraicGeometry.AbelianScheme.CentralAction.PoweredSideFinite.Construction

end

end OAI
