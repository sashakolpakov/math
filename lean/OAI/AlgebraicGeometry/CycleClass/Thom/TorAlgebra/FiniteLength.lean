import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Finite
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Support
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Finite Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteLength.Tor

noncomputable section

/-! A finite module with at most one support point has finite length.
Together with Tor support containment, this proves finite Tor length for
isolated intersections in a local spectrum. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

theorem finiteLength_of_support_subsingleton (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton (Module.support R M)] : IsFiniteLength R M := by
  let A := R ⧸ Module.annihilator R M
  have hd : ringKrullDim A ≤ 0 := by
    rw [← Module.supportDim_eq_ringKrullDim_quotient_annihilator]
    exact Order.krullDim_nonpos_of_subsingleton
  let : Ring.KrullDimLE 0 A := ⟨hd⟩
  let : IsArtinianRing A := isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  let : Module A M := Module.quotientAnnihilator (R := R) (M := M)
  let : IsScalarTower R A M := (Module.isTorsionBySet_annihilator R M).isScalarTower
  let : Module.Finite A M := Module.Finite.of_restrictScalars_finite R A M
  let : IsArtinian R M := isArtinian_of_surjective_algebraMap
    (show Function.Surjective (algebraMap R A) from Ideal.Quotient.mk_surjective)
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

theorem finiteLength_of_support_subset_singleton
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (h : Module.support R M ⊆ {p}) : IsFiniteLength R M := by
  let : Subsingleton (Module.support R M) := ⟨fun a b => Subtype.ext
    ((Set.mem_singleton_iff.mp (h a.property)).trans (Set.mem_singleton_iff.mp (h b.property)).symm)⟩
  exact finiteLength_of_support_subsingleton R M

theorem tor_finiteLength (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (p : PrimeSpectrum R)
    (h : Module.support R M ∩ Module.support R N ⊆ {p}) (n : ℕ) :
    IsFiniteLength R (((Tor (ModuleCat R) n).obj M).obj N) := by
  let := TorAlgebra.Finite.Tor.finite R M N n
  exact finiteLength_of_support_subset_singleton R _ p ((Support.Tor.support_subset R M N n).trans h)

theorem tor_length_ne_top (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (p : PrimeSpectrum R)
    (h : Module.support R M ∩ Module.support R N ⊆ {p}) (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj M).obj N) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (tor_finiteLength R M N p h n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteLength.Tor
