import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Annihilator
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.LocalFree
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # Prime Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimePrincipal

noncomputable section

/-! In a noetherian local ring whose residue field has projective
dimension at most two, every nonmaximal prime ideal is principal. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

theorem residue_annihilated (r : R) (hr : r ∈ maximalIdeal R)
    (x : ResidueField R) : r • x = 0 := by
  rw [Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff r).mpr hr, zero_mul]

theorem regular_tor_vanishing (M : ModuleCat.{u} R) (r : R)
    (hr : r ∈ maximalIdeal R) (hm : IsSMulRegular M r) (d : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) d] :
    IsZero (((Tor (ModuleCat R) d).obj M).obj
      (ModuleCat.of R (ResidueField R))) :=
  ProjectionFormula.Tor.Annihilator.isZero_of_regular R M (ModuleCat.of R (ResidueField R)) r hm
    (residue_annihilated R r hr) d
    (BoundedResolution.tor_isZero R (ModuleCat.of R (QuotSMulTop r M))
      (ModuleCat.of R (ResidueField R)) d (d + 1) (by omega))

variable [IsNoetherianRing R]
  [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) 2]

theorem prime_free (p : Ideal R) [p.IsPrime] (hp : p ≠ maximalIdeal R) : Module.Free R p := by
  have hprime : p.IsPrime := inferInstance
  have hlt : p < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal hprime.ne_top) hp
  obtain ⟨r, hr, hrp⟩ := SetLike.exists_of_lt hlt
  have hreg : IsSMulRegular (R ⧸ p) r := by
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro x hx
    exact (hprime.mem_or_mem hx).resolve_left hrp
  have hz := regular_tor_vanishing R (ModuleCat.of R (R ⧸ p)) r hr hreg 2
  let S := IsolatedTorEuler.submoduleSequence R (ModuleCat.of R R) p
  have hS := IsolatedTorEuler.submoduleSequence_shortExact R (ModuleCat.of R R) p
  let : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of R R))
  let e := ProjectionFormula.Tor.FirstShift.shiftIso R (ModuleCat.of R (ResidueField R)) S hS 0
  let : Module.FinitePresentation R p := Module.finitePresentation_of_finite R p
  exact ProjectionFormula.Tor.LocalFree.of_residue_second R (ModuleCat.of R p) (hz.of_iso e.symm)

theorem prime_principal (p : Ideal R) [p.IsPrime] (hp : p ≠ maximalIdeal R) :
    p.IsPrincipal := by
  let := prime_free R p hp
  apply (Submodule.rank_le_one_iff_isPrincipal p).mp
  exact (Submodule.rank_le p).trans_eq (Module.rank_self R)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimePrincipal
