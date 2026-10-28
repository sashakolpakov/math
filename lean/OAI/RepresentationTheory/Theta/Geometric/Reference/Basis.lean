import OAI.RepresentationTheory.Theta.Geometric.Period.Lattice

/-! # Basis -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! One integral basis of the fixed reference lattice gives compatible
bases in every explicit period fiber. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.periodLatticeMap (x : D.domain) : D.pel.reference.lattice →+ D.periodLattice x.val where
  toFun v := ⟨D.periodReferenceEmbedding x.val v.val,
    (D.periodLattice_mem x.val _).mpr ⟨v.val, v.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (D.periodReferenceEmbedding x.val))
  map_add' v w := Subtype.ext (map_add (D.periodReferenceEmbedding x.val) v.val w.val)

theorem Data.ActiveHeckeThetaData.periodLatticeMap_bijective (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Function.Bijective (D.periodLatticeMap x) := by
  constructor
  · intro v w h
    apply Subtype.ext
    exact (D.referenceAnalyticFiber hg x).periodReferenceEmbedding_injective D hg
      (congrArg Subtype.val h)
  · intro t
    obtain ⟨v, hv, he⟩ := (D.periodLattice_mem x.val t.val).mp t.property
    exact ⟨⟨v, hv⟩, Subtype.ext he⟩

def Data.ActiveHeckeThetaData.periodLatticeEquiv (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    D.pel.reference.lattice ≃ₗ[ℤ] (D.canonicalPeriodData hg x).periodIntegerLattice :=
  (AddEquiv.ofBijective (D.periodLatticeMap x) (D.periodLatticeMap_bijective hg x)).toIntLinearEquiv

@[simp] theorem Data.ActiveHeckeThetaData.periodLatticeEquiv_apply (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (v : D.pel.reference.lattice) :
    (D.periodLatticeEquiv hg x v).val = D.periodReferenceEmbedding x.val v.val := rfl

theorem Data.ActiveHeckeThetaData.periodLattice_rank (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Module.finrank ℤ (D.canonicalPeriodData hg x).periodIntegerLattice = 2 * (3 * s) := by
  rw [ZLattice.rank ℝ (D.canonicalPeriodData hg x).periodIntegerLattice]
  change Module.finrank ℝ (Fin s → Fin 3 → ℂ) = _
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

def Data.ActiveHeckeThetaData.periodOrigin (hg : D.pel.HasIntegralModelGeometry) : D.domain :=
  ⟨0, by
    have h := hg.reference_admissible.2.2.2.1
    change Complex.normSq 0 + Complex.normSq 0 < -(D.pel.reference.μ D.pel.reference.b).re
    simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr h⟩

def Data.ActiveHeckeThetaData.referenceBasis (hg : D.pel.HasIntegralModelGeometry) :
    Module.Basis (Fin (2 * (3 * s))) ℤ D.pel.reference.lattice := by
  let x := D.periodOrigin hg
  let L := (D.canonicalPeriodData hg x).periodIntegerLattice
  let : Module.Free ℤ L := ZLattice.module_free ℝ L
  let : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  exact ((Module.finBasis ℤ L).reindex (finCongr (D.periodLattice_rank hg x))).map
    (D.periodLatticeEquiv hg x).symm

def Data.ActiveHeckeThetaData.periodBasis (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Module.Basis (Fin (2 * (3 * s))) ℤ (D.canonicalPeriodData hg x).periodIntegerLattice :=
  (D.referenceBasis hg).map (D.periodLatticeEquiv hg x)

@[simp] theorem Data.ActiveHeckeThetaData.periodBasis_apply (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (i : Fin (2 * (3 * s))) :
    (D.periodBasis hg x i).val = D.periodReferenceEmbedding x.val (D.referenceBasis hg i).val := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
