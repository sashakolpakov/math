import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PEL
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarTateLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport

/-! # Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Lattices.Construction

noncomputable section

/-! Chosen and opposite lattices of the actual one-step central isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

theorem framedTateLattice_castMultiplier {R : Type} [CommRing R] {S : Scheme}
    {g N s q n m : ℕ} [Fact q.Prime] {A B : TateComparison.PEL.PELFamilyData R g N S}
    {T : Over S} (e : TateComparison.Rational.SplitTateFrame s A.abelian.scheme T q)
    (f : TateComparison.PELIsogenies.PELIsogeny A B n) (h : n = m) (i : Fin s × Bool) :
    TateComparison.Rational.framedTateLattice e (f.castMultiplier h).isogeny.hom i =
      TateComparison.Rational.framedTateLattice e f.isogeny.hom i := by
  cases h
  rfl

theorem dualSubmodule_unit_smul {R K V : Type*}
    [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V]
    (B : LinearMap.BilinForm K V) (L : Submodule R V) (u : Kˣ) :
    B.dualSubmodule (u • L) = u⁻¹ • B.dualSubmodule L := by
  apply Submodule.ext
  intro x
  change (∀ y ∈ u • (L : Set V), B x y ∈ (1 : Submodule R K)) ↔
    x ∈ u⁻¹ • (B.dualSubmodule L : Set V)
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [inv_inv]
  constructor
  · intro hx y hy
    have hh := hx (u • y) (Set.smul_mem_smul_set hy)
    simpa only [Units.smul_def, map_smul, LinearMap.smul_apply] using hh
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hh := hx z hz
    simpa only [Units.smul_def, map_smul, LinearMap.smul_apply] using hh

theorem pi_submodule_project {R K V : Type*} {Idx : Type*} [DecidableEq Idx]
    [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V]
    (L : Idx → Submodule R V) (i : Idx) :
    (Submodule.pi Set.univ L).map
      ((LinearMap.proj i : (Idx → V) →ₗ[K] V).restrictScalars R) = L i := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Submodule.mem_pi.mp hz) i (Set.mem_univ _)
  · intro hx
    refine ⟨Pi.single i x, ?_, by simp⟩
    apply Submodule.mem_pi.mpr
    intro j _
    by_cases hj : j = i
    · subst j
      simpa using hx
    · simp [Pi.single_eq_of_ne hj]

theorem scalar_framedTateLattice
    {E : Type} [Field E] {S : Scheme} {g N s m q : ℕ} [Fact q.Prime]
    (P : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S) (T : Over S)
    (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
    (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q) (he : TateComparison.Rational.IsSplitActionFrame P T q χ e)
    (L : Fin s × Bool → Submodule ℤ_[q] (Fin 3 → ℚ_[q]))
    (hL : TateComparison.Rational.framedIntegralTateImage e = Submodule.pi Set.univ L)
    (b : NumberField.RingOfIntegers E) (a : Fin s × Bool → ℕ)
    (hlocal : ∀ i, ∃ u : ℤ_[q]ˣ, χ i b = (q : ℤ_[q]) ^ a i * u)
    (f : TateComparison.PELIsogenies.PELIsogeny P P m) (hf : f.isogeny.hom = Scalar.Construction.scalarMap P b) (i : Fin s × Bool) :
    TateComparison.Rational.framedTateLattice e f.isogeny.hom i = (TateComparison.HeckeKernel.qUnit q ^ (-(a i : ℤ))) • L i := by
  change (TateLattices.Construction.framedTatePreimage T e f).map _ = _
  rw [ScalarTateLattice.Construction.scalar_framedTatePreimage q P T χ e he L hL b a hlocal f hf]
  exact pi_submodule_project _ i

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

/-- TateComparison supplies an actual central PEL isogeny to the graph endpoint,
and determines both sides of its intrinsic lattice in one source frame. -/
theorem exists_central_fiber_isogeny_lattices
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hflags : D.HasPolarizedFlagRealizations hIsogenyQuotient)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ) (ha : ∀ v i, t.val.exponent v i = a v)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x : D.GeometricPoint b) :
    ∃ (e : D.FiberFrame b x)
      (B : Fin s → LinearMap.BilinForm ℚ_[q] (Fin 3 → ℚ_[q]))
      (L : Fin s → TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q])
      (y : D.GeometricPoint b)
      (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ t.multiplierNat)),
      D.IsIntegralSplitFrame b x e B L ∧
      y = x ≫ PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hflags t a ha ∧
      ∀ v : Fin s,
        TateComparison.Rational.framedTateLattice e f.isogeny.hom (v, false) =
          (TateComparison.HeckeKernel.qUnit q ^ (-a v)) • (L v).val ∧
        TateComparison.Rational.framedTateLattice e f.isogeny.hom (v, true) =
          (TateComparison.HeckeKernel.qUnit q ^ (-(t.val.multiplier - a v))) • (B v).dualSubmodule (L v).val := by
  have := PEL.Construction.central_correspondence_source_isIso D hgeometry hIsogenyQuotient hflags t a ha
  let c := x ≫ inv (D.correspondence t).source
  have hc : c ≫ (D.correspondence t).source = x := by simp [c]
  let F := PEL.Construction.singletonPELFlag D t x c hc
  obtain ⟨e, B, L, _, he, hh⟩ := hflags k b x
  obtain ⟨eqv, comp, hreal, _⟩ := hh [t]
  obtain ⟨p, steps, _, _, hlat⟩ := hreal F
  have hflag := Flags.Construction.central_singleton_flag_unique q L t a ha (eqv F)
  have hm : TateComparison.Data.SphericalPELAlbaneseData.flagMultiplier [t] (1 : Fin 2) = t.multiplierNat := by
    simp [TateComparison.Data.SphericalPELAlbaneseData.flagMultiplier, TateComparison.Local.cumulativeMultiplier,
      TateComparison.Local.IntegralType.multiplierNat]
  let f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b (F.point 1))
      (q ^ t.multiplierNat) := (p (1 : Fin 2)).castMultiplier (congrArg (q ^ ·) hm)
  refine ⟨e, B, L, F.point 1, f, he, ?_, ?_⟩
  · change c ≫ (D.correspondence t).target = _
    rw [← PEL.Construction.centralModuliMap_source D hgeometry hIsogenyQuotient hflags t a ha,
      ← Category.assoc, hc]
  · intro v
    have hl := hlat (1 : Fin 2) v
    rw [hflag] at hl
    have hl' :
        TateComparison.Rational.framedTateLattice e (p (1 : Fin 2)).isogeny.hom (v, false) =
          (TateComparison.HeckeKernel.qUnit q ^ (-a v)) • (L v).val ∧
        TateComparison.Rational.framedTateLattice e (p (1 : Fin 2)).isogeny.hom (v, true) =
          (TateComparison.HeckeKernel.qUnit q ^ (-t.val.multiplier)) •
            (B v).dualSubmodule ((TateComparison.HeckeKernel.qUnit q ^ (-a v)) • (L v).val) := by
      simpa [TateComparison.Data.SphericalPELAlbaneseData.compositeLattice, Flags.Construction.centralSingletonFlag,
        Flags.Construction.centralScaledLattice, TateComparison.Local.cumulativeMultiplier] using hl
    rw [dualSubmodule_unit_smul, ← zpow_neg, neg_neg, smul_smul,
      ← zpow_add] at hl'
    have hi : -t.val.multiplier + a v = -(t.val.multiplier - a v) := by omega
    rw [hi] at hl'
    dsimp only [f]
    simp only [framedTateLattice_castMultiplier]
    exact hl'

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Lattices.Construction
