import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSheafPurity

/-! # Good Shift Cohomology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions

noncomputable section

section

/-! Canonical truncation shifts actual cohomology, including its new degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]

def cochainGoodShiftHomologyIso (K : CochainComplex C ℕ) (k n : ℕ) :
    (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).homology n ≅ K.homology (k+n) := by
  let e := RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k
  have : QuasiIsoAt (K.πTruncGE e) (k+n) := K.quasiIsoAt_πTruncGE e (j := n) rfl
  exact ((K.truncGE' e).extendHomologyIso e (j := n) (j' := k+n) rfl).symm ≪≫
    (isoOfQuasiIsoAt (K.πTruncGE e) (k+n)).symm

theorem cochainGoodTruncation_quasiIso (K : CochainComplex C ℕ) (k : ℕ)
    (hK : ∀ n, n<k → K.ExactAt n) : QuasiIso (K.πTruncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) := by
  apply (K.quasiIso_πTruncGE_iff_isSupported (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).mpr
  constructor
  intro n hn
  apply hK n
  by_contra h
  have he : (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).f (n-k) = n := by
    change k+(n-k)=n
    omega
  exact hn (n-k) he

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

abbrev regularThomGoodShiftSheafComplex := Z.regularThomSheafComplex.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2*p))

def regularThomGoodShift_zeroHomologyIso :
    (regularThomGoodShiftSheafComplex Z).homology 0 ≅ Z.regularThomSheafComplex.homology (2*p) :=
  cochainGoodShiftHomologyIso Z.regularThomSheafComplex (2*p) 0

theorem regularThomGoodShift_positive_homology_isZero (n : ℕ) (hn : 0<n) :
    IsZero ((regularThomGoodShiftSheafComplex Z).homology n) :=
  (RegularThomSheafPurity.Constructions.regularThomSheaf_homology_isZero_except Z (2*p+n) (by omega)).of_iso
    (cochainGoodShiftHomologyIso Z.regularThomSheafComplex (2*p) n)

theorem regularThomGoodTruncation_quasiIso :
    QuasiIso (Z.regularThomSheafComplex.πTruncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2*p))) :=
  cochainGoodTruncation_quasiIso Z.regularThomSheafComplex (2*p)
    (fun n hn => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z n (by omega))

end

/-! The canonical good-shift cohomology isomorphism acts on the original actual cycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℕ) (k n : ℕ)

def cochainGoodShiftCyclesMap : K.cycles (k+n) ⟶
    (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).cycles n :=
  cyclesMap (K.πTruncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) (k+n) ≫
    ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).extendCyclesIso
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) (j := n) (j' := k+n) rfl).hom

theorem cochainGoodShiftCyclesMap_inclusion :
    cochainGoodShiftCyclesMap K k n ≫ (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).iCycles n =
      K.iCycles (k+n) ≫ (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n := by
  unfold cochainGoodShiftCyclesMap
  rw [Category.assoc, extendCyclesIso_hom_iCycles, ← Category.assoc]
  change (cyclesMap (K.πTruncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) (k+n) ≫
      (K.truncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).iCycles (k+n)) ≫
      ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).extendXIso (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)
        (i := n) (i' := k+n) rfl).hom = _
  rw [cyclesMap_i, Category.assoc]
  rw [πTruncGE, (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).liftExtend_f _ _ (i := n) (i' := k+n) rfl]
  simp only [restrictionXIso, eqToIso_refl, Iso.refl_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change K.iCycles (k+n) ≫ 𝟙 (K.X (k+n)) ≫
    (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n = _
  rw [Category.id_comp]

theorem cochainGoodShiftCyclesMap_homologyπ :
    cochainGoodShiftCyclesMap K k n ≫ (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).homologyπ n ≫
        (cochainGoodShiftHomologyIso K k n).hom = K.homologyπ (k+n) := by
  let e := RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k
  let T := K.truncGE' e
  have : QuasiIsoAt (K.πTruncGE e) (k+n) := K.quasiIsoAt_πTruncGE e (j := n) rfl
  change (cyclesMap (K.πTruncGE e) (k+n) ≫ (T.extendCyclesIso e (j := n) (j' := k+n) rfl).hom) ≫
    T.homologyπ n ≫ ((T.extendHomologyIso e (j := n) (j' := k+n) rfl).inv ≫
      (isoOfQuasiIsoAt (K.πTruncGE e) (k+n)).inv) = K.homologyπ (k+n)
  rw [Category.assoc, ← Category.assoc (T.extendCyclesIso e rfl).hom,
    ← homologyπ_extendHomologyIso_hom, Category.assoc]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  change (cyclesMap (K.πTruncGE e) (k+n) ≫ (K.truncGE e).homologyπ (k+n)) ≫
    (isoOfQuasiIsoAt (K.πTruncGE e) (k+n)).inv = _
  rw [← homologyπ_naturality, Category.assoc, isoOfQuasiIsoAt_hom_inv_id,
    Category.comp_id]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions
