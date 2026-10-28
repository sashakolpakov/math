import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.Annihilator
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Ideal Sheaf Nilpotence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealSheafNilpotence

noncomputable section

/-! On a noetherian quasi-compact scheme, containment of closed supports
gives one global power containment for the actual ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem idealSheaf_exists_power_le_of_support_le
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (I J : X.IdealSheafData) (h : J.support ≤ I.support) :
    ∃ n : ℕ, I ^ n ≤ J := by
  classical
  have hr : I ≤ J.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h
  let C := X.affineCover.finiteSubcover
  have (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C]
    infer_instance
  let U : C.I₀ → X.affineOpens := fun i =>
    ⟨(C.f i).opensRange, isAffineOpen_opensRange (C.f i)⟩
  have hn (i : C.I₀) : ∃ n : ℕ, (I.ideal (U i)) ^ n ≤ J.ideal (U i) := by
    have : IsNoetherianRing Γ(X, (U i).1) := IsLocallyNoetherian.component_noetherian (U i)
    exact Ideal.exists_pow_le_of_le_radical_of_fg (hr (U i))
      (I.ideal (U i)).fg_of_isNoetherianRing
  choose n hn using hn
  let : Fintype C.I₀ := Fintype.ofFinite C.I₀
  let b := Finset.univ.sup n
  refine ⟨b, Scheme.IdealSheafData.le_of_iSup_eq_top U C.iSup_opensRange ?_⟩
  intro i
  change (I.ideal (U i)) ^ b ≤ J.ideal (U i)
  exact (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i))).trans (hn i)

theorem coherent_support_exists_annihilating_ideal_power
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (I : X.IdealSheafData)
    (h : (Coherent.Annihilator.coherentAnnihilator M).support ≤ I.support) :
    ∃ n : ℕ, ∀ U : X.affineOpens, ∀ r ∈ (I.ideal U) ^ n,
      ∀ m : Γ(M, U.1), r • m = 0 := by
  obtain ⟨n, hn⟩ := idealSheaf_exists_power_le_of_support_le I (Coherent.Annihilator.coherentAnnihilator M) h
  exact ⟨n, fun U r hr => Module.mem_annihilator.mp (hn U hr)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealSheafNilpotence
