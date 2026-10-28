import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Lattices
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizedKernels
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GenericModuli

/-! # Scalar Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarKernels.Construction

noncomputable section

/-! The local principal scalar and the actual central correspondence have
the same entire geometric kernel. Compatibility is deduced from the TateComparison
flag conclusion and the explicit local scalar exponents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open scoped _root_.CategoryTheory.MonObj Pointwise

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def centralBlockExponent (t : TateComparison.Local.IntegralType s) (i : Fin s × Bool) : ℕ :=
  if i.2 then t.multiplierNat - t.exponentNat i.1 0 else t.exponentNat i.1 0

theorem fiber_preimage_eq_of_lattices
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgood : D.IsGoodCompletelySplitPrime)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x y : D.GeometricPoint b) {n m : ℕ}
    (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) n)
    (g : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b x) m)
    (e : D.FiberFrame b x) (ey : D.FiberFrame b y)
    (B By : Fin s → LinearMap.BilinForm ℚ_[q] (Fin 3 → ℚ_[q]))
    (L Ly : Fin s → TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q])
    (he : D.IsIntegralSplitFrame b x e B L) (hey : D.IsIntegralSplitFrame b y ey By Ly)
    (hlat : ∀ i, TateComparison.Rational.framedTateLattice e f.isogeny.hom i = TateComparison.Rational.framedTateLattice e g.isogeny.hom i) :
    TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) g.isogeny.hom := by
  have cmp := TateLattices.Construction.intrinsic_preimage_eq_of_framed_lattices
    (P := D.fiberFamily b x) (Q := D.fiberFamily b y) (Q' := D.fiberFamily b x)
    (s := s) (q := q) (n := n) (m := m)
    (Over.mk (𝟙 (Spec (.of k)))) D.localCharacter
    (SplitScalar.Construction.localCharacter_separates D hgood)
  have cmp' := cmp e ey e
  have cmp'' := cmp' he.1 hey.1 he.1
  have cmp''' := cmp''
    (fun i => if i.2 then (By i.1).dualSubmodule (Ly i.1).val else (Ly i.1).val)
    (fun i => if i.2 then (B i.1).dualSubmodule (L i.1).val else (L i.1).val)
    hey.2 he.2
  apply cmp''' f g
  intro i
  exact hlat i

theorem fiber_kernel_eq_of_preimage
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x y : D.GeometricPoint b) (n : ℕ)
    (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ n))
    (g : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b x) (q ^ n))
    (hpre : TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) g.isogeny.hom)
    (z : Over.mk (𝟙 (Spec (.of k))) ⟶ (D.fiberFamily b x).abelian.scheme) :
    z ≫ f.isogeny.hom = 1 ↔ z ≫ g.isogeny.hom = 1 := by
  have hpol := GenericModuli.Construction.generic_family_polarizationType D hgeometry
  have cmp := PolarizedKernels.Construction.pelIsogeny_geometricKernel_eq_of_TatePreimage
    (K := K) (R := 𝓞 E) (S := Spec (.of k)) (g := 3 * s) (N := D.level)
    (D.fiberFamily b x) (D.fiberFamily b y) (D.fiberFamily b x) b
    D.reference.polarizationType (hpol.pullback x.left) (hpol.pullback y.left)
    (hpol.pullback x.left) q n n
  have cmp' := cmp f g (𝟙 (Spec (.of k)))
  apply cmp' _ z
  exact hpre

/-- For an integral central type, an explicit scalar with the same local
exponents yields the same full geometric kernel as an actual isogeny to
the central graph endpoint. No scalar/correspondence compatibility is an input. -/
theorem central_scalar_geometric_kernel_comparison
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hflags : D.HasPolarizedFlagRealizations hIsogenyQuotient)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ) (ha : ∀ v i, t.val.exponent v i = a v)
    (β : 𝓞 E)
    (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = (q : 𝓞 E) ^ t.multiplierNat)
    (hmark : Marking.Construction.levelReduction E D.level β = 1)
    (hlocal : ∀ i, ∃ u : ℤ_[q]ˣ,
      D.localCharacter i β = (q : ℤ_[q]) ^ centralBlockExponent t i * u)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x : D.GeometricPoint b) :
    ∃ (y : D.GeometricPoint b)
      (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ t.multiplierNat)),
      y = x ≫ PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hflags t a ha ∧
      ∀ z : Over.mk (𝟙 (Spec (.of k))) ⟶ (D.fiberFamily b x).abelian.scheme,
        z ≫ f.isogeny.hom = 1 ↔ z ≫ Scalar.Construction.scalarMap (D.fiberFamily b x) β = 1 := by
  obtain ⟨e, B, L, y, f, he, hy, hlat⟩ :=
    Lattices.Construction.exists_central_fiber_isogeny_lattices D hgeometry hIsogenyQuotient hflags t a ha b x
  obtain ⟨ey, By, Ly, _, hey, _⟩ := hflags k b y
  have hnorm' : β * IsCMField.ringOfIntegersComplexConj E β = (q ^ t.multiplierNat : ℕ) := by
    simpa only [Nat.cast_pow] using hnorm
  let scalar := ScalarIsogeny.Construction.scalarPELIsogeny_of_norm D.family D.space.hom
    (GenericModuli.Construction.generic_family_rosati D hgeometry) β (q ^ t.multiplierNat)
    (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) hnorm' hmark
  let scalarX : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b x)
      (q ^ t.multiplierNat) := scalar.pullback x.left
  have hscalar : scalarX.isogeny.hom = Scalar.Construction.scalarMap (D.fiberFamily b x) β := by
    exact (D.family.pullback_action_schemeMap x.left β).symm
  let LX (i : Fin s × Bool) := if i.2 then (B i.1).dualSubmodule (L i.1).val else (L i.1).val
  have hlat_eq (i : Fin s × Bool) :
      TateComparison.Rational.framedTateLattice e f.isogeny.hom i = TateComparison.Rational.framedTateLattice e scalarX.isogeny.hom i := by
    rw [Lattices.Construction.scalar_framedTateLattice (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k))))
      D.localCharacter e he.1 LX he.2 β (centralBlockExponent t) hlocal scalarX hscalar i]
    obtain ⟨v, w⟩ := i
    have ha' : (t.exponentNat v 0 : ℤ) = a v := (t.exponentNat_cast v 0).trans (ha v 0)
    cases w
    · change TateComparison.Rational.framedTateLattice e f.isogeny.hom (v, false) =
        (TateComparison.HeckeKernel.qUnit q ^ (-(t.exponentNat v 0 : ℤ))) • (L v).val
      rw [ha']
      exact (hlat v).1
    · change TateComparison.Rational.framedTateLattice e f.isogeny.hom (v, true) =
        (TateComparison.HeckeKernel.qUnit q ^ (-((t.multiplierNat - t.exponentNat v 0 : ℕ) : ℤ))) •
          (B v).dualSubmodule (L v).val
      rw [Int.ofNat_sub (t.exponentNat_le v 0), t.multiplierNat_cast, ha']
      exact (hlat v).2
  have hpre : TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) scalarX.isogeny.hom := by
    exact fiber_preimage_eq_of_lattices D hgood b x y f scalarX e ey B By L Ly he hey hlat_eq
  refine ⟨y, f, hy, ?_⟩
  intro z
  rw [← hscalar]
  apply fiber_kernel_eq_of_preimage D hgeometry b x y t.multiplierNat f scalarX _ z
  exact hpre

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarKernels.Construction
