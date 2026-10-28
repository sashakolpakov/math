import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredKernels
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricQuotients

/-! # Powered Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredQuotients.Construction

noncomputable section

/-! Actual scalar quotient comparisons for uniform powers of the central
moduli automorphisms, preserving the integral action and the full marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def fiberScalarIsogeny
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (β : 𝓞 E) (n : ℕ) (hn : n ≠ 0)
    (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = n)
    (hmark : Marking.Construction.levelReduction E D.level β = 1)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x : D.GeometricPoint b) : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b x) n :=
  (ScalarIsogeny.Construction.scalarPELIsogeny_of_norm D.family D.space.hom (GenericModuli.Construction.generic_family_rosati D hgeometry)
    β n hn hnorm hmark).pullback x.left

theorem fiberScalarIsogeny_hom
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (β : 𝓞 E) (n : ℕ) (hn : n ≠ 0)
    (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = n)
    (hmark : Marking.Construction.levelReduction E D.level β = 1)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x : D.GeometricPoint b) :
    (fiberScalarIsogeny D hgeometry β n hn hnorm hmark b x).isogeny.hom =
      Scalar.Construction.scalarMap (D.fiberFamily b x) β :=
  (D.family.pullback_action_schemeMap x.left β).symm

/-- The Finiteness scalar comparison now yields a genuine group-scheme
isomorphism from the powered graph endpoint back to the source abelian
variety, together with all integral-action and full-marking equations. -/
theorem exists_powered_side_scalar_quotients
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
    (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
    (hFiniteness : Arithmetic.Construction.PrincipalizationInput E) (side : Fin s → Bool) :
    ∃ (n : ℕ) (β : 𝓞 E), 0 < n ∧ β ≠ 0 ∧
      β * IsCMField.ringOfIntegersComplexConj E β = (q : 𝓞 E) ^ n ∧
      Marking.Construction.levelReduction E D.level β = 1 ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
        (x : D.GeometricPoint b),
        ∃ (y : D.GeometricPoint b)
          (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ n))
          (j : (D.fiberFamily b y).abelian.scheme ≅ (D.fiberFamily b x).abelian.scheme),
          y = x ≫ Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison
            (PoweredKernels.Construction.sideChosenExponent side) 1 (PoweredKernels.Construction.sideChosenExponent_le_one side) ^ n ∧
          IsMonHom j.hom ∧ f.isogeny.hom ≫ j.hom = Scalar.Construction.scalarMap (D.fiberFamily b x) β ∧
          (∀ r : 𝓞 E,
            Scalar.Construction.scalarMap (D.fiberFamily b y) r ≫ j.hom = j.hom ≫ Scalar.Construction.scalarMap (D.fiberFamily b x) r) ∧
          ∀ (T : Over (Spec (.of k)))
            (c : LocallyConstant T.left (Multiplicative (Fin (2 * (3 * s)) → ZMod D.level))),
            ((D.fiberFamily b y).marking.hom.app (.op T) c).val ≫ j.hom =
              ((D.fiberFamily b x).marking.hom.app (.op T) c).val := by
  obtain ⟨n, β, hn, hb, hnorm, hmark, hh⟩ :=
    PoweredKernels.Construction.exists_powered_side_scalar_kernels D hgeometry hgood hdegree hIsogenyQuotient A hTateComparison hFiniteness side
  refine ⟨n, β, hn, hb, hnorm, hmark, ?_⟩
  intro k _ _ b x
  obtain ⟨y, f, hy, hker⟩ := hh k b x
  have hnq : q ^ n ≠ 0 := pow_ne_zero _ (Fact.out : q.Prime).ne_zero
  have hnorm' : β * IsCMField.ringOfIntegersComplexConj E β = (q ^ n : ℕ) := by
    simpa only [Nat.cast_pow] using hnorm
  let e := fiberScalarIsogeny D hgeometry β (q ^ n) hnq hnorm' hmark b x
  have he : e.isogeny.hom = Scalar.Construction.scalarMap (D.fiberFamily b x) β :=
    fiberScalarIsogeny_hom D hgeometry β (q ^ n) hnq hnorm' hmark b x
  have hker' : ∀ z : Over.mk (𝟙 (Spec (.of k))) ⟶ (D.fiberFamily b x).abelian.scheme,
      z ≫ f.isogeny.hom = 1 ↔ z ≫ e.isogeny.hom = 1 := by
    intro z
    rw [he]
    exact hker z
  have hpol := (GenericModuli.Construction.generic_family_polarizationType D hgeometry).pullback x.left
  have hunit := ScalarIsogeny.Construction.nat_unit_on_charZero_scheme b (q ^ n) hnq
  obtain ⟨j, hj, hfac, hact, hlevel⟩ :=
    GeometricQuotients.Construction.exists_pel_quotient_group_iso_of_geometric_kernel f e D.reference.polarizationType
      hpol hunit hunit hker'
  refine ⟨y, f, j, hy, hj, hfac.trans he, hact, hlevel⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredQuotients.Construction
