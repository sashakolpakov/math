import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology
import Mathlib.Algebra.Homology.SingleHomology

/-! # Thom Good Shift Flasque -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions

noncomputable section

section

/-! The canonical augmentation of the actual shifted supported Thom complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]

def cochainZeroHomologyAugmentation (K : CochainComplex C ℕ) :
    (CochainComplex.single₀ C).obj (K.homology 0) ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K (K.homology 0)).symm
    ⟨K.isoHomologyπ₀.inv ≫ K.iCycles 0, by rw [Category.assoc, K.iCycles_d, comp_zero]⟩

theorem cochainZeroHomologyAugmentation_f_zero (K : CochainComplex C ℕ) :
    (cochainZeroHomologyAugmentation K).f 0 = K.isoHomologyπ₀.inv ≫ K.iCycles 0 :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

theorem cochainZeroHomologyAugmentation_cycles (K : CochainComplex C ℕ) :
    HomologicalComplex.cyclesMap (cochainZeroHomologyAugmentation K) 0 =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (K.homology 0)).hom ≫
        K.isoHomologyπ₀.inv := by
  apply (cancel_mono (K.iCycles 0)).mp
  rw [HomologicalComplex.cyclesMap_i, cochainZeroHomologyAugmentation_f_zero]
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom]
  change _ = ((_ ≫ 𝟙 _) ≫ _) ≫ _
  simp only [Category.comp_id, Category.assoc]

theorem cochainZeroHomologyAugmentation_homology (K : CochainComplex C ℕ) :
    HomologicalComplex.homologyMap (cochainZeroHomologyAugmentation K) 0 =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (K.homology 0)).hom := by
  apply (cancel_epi (((CochainComplex.single₀ C).obj (K.homology 0)).homologyπ 0)).mp
  rw [HomologicalComplex.homologyπ_naturality, cochainZeroHomologyAugmentation_cycles,
    Category.assoc, HomologicalComplex.isoHomologyπ_inv_hom_id,
    Category.comp_id, HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]

theorem cochainZeroHomologyAugmentation_quasiIso (K : CochainComplex C ℕ)
    (hK : ∀ n, 0<n → IsZero (K.homology n)) :
    QuasiIso (cochainZeroHomologyAugmentation K) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rcases n with _ | n
  · rw [cochainZeroHomologyAugmentation_homology]
    infer_instance
  · exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℕ) 0
      (K.homology 0) (n+1) (by omega)).isIso (hK (n+1) (by omega)) _

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

/-- The orientation sheaf, placed in degree zero, maps into the canonical good shift. -/
def regularThomSheafAugmentation :
    (CochainComplex.single₀ _).obj (Z.regularThomSheafComplex.homology (2*p)) ⟶
      GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z :=
  (CochainComplex.single₀ _).map (GoodShiftCohomology.Constructions.regularThomGoodShift_zeroHomologyIso Z).inv ≫
    cochainZeroHomologyAugmentation (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)

theorem regularThomSheafAugmentation_quasiIso : QuasiIso (regularThomSheafAugmentation Z) := by
  have := cochainZeroHomologyAugmentation_quasiIso (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (GoodShiftCohomology.Constructions.regularThomGoodShift_positive_homology_isZero Z)
  unfold regularThomSheafAugmentation
  infer_instance

end

/-! The canonical shifted Thom complex is an actual flasque resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

theorem rationalSheafFlasque_of_forget (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    [TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).obj F)] : TopCat.Sheaf.IsFlasque F where
  epi i := by
    have h : Epi (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (F.obj.map i)) :=
      inferInstanceAs (Epi (((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).obj F).obj.map i))
    exact AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.epi_of_epi_map h

theorem rationalSheafFlasque_of_iso {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (e : F ≅ G) [TopCat.Sheaf.IsFlasque F] : TopCat.Sheaf.IsFlasque G := by
  have : TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).obj G) :=
    CycleClass.Geometric.FlasqueLowDegree.Cycles.flasqueSheaf_of_iso ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).mapIso e)
  exact rationalSheafFlasque_of_forget G

theorem rationalFlasque_opcycles_of_exact_below
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (k : ℕ) (he : ∀ n, n<k → K.ExactAt n) (n : ℕ) (hn : n≤k) :
    TopCat.Sheaf.IsFlasque (K.opcycles n) := by
  have hKA : ∀ i, TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K).X i) := by
    intro i
    have := hK i
    exact AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget_isFlasque (K.X i)
  have hKe : ∀ i, i<k → (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K).ExactAt i := by
    intro i hi
    exact (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex_exactAt_iff K i).mpr (he i hi)
  have := CycleClass.Geometric.FlasqueLowDegree.Cycles.flasque_opcycles_of_exact_below (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K) hKA k hKe n hn
  have : TopCat.Sheaf.IsFlasque (((K.sc n).map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X)).opcycles) :=
    inferInstanceAs (TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K).opcycles n))
  have : TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).obj (K.opcycles n)) :=
    CycleClass.Geometric.FlasqueLowDegree.Cycles.flasqueSheaf_of_iso ((K.sc n).mapOpcyclesIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X))
  exact rationalSheafFlasque_of_forget (K.opcycles n)

theorem rationalGoodShift_isFlasque
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (k : ℕ) (he : ∀ n, n<k → K.ExactAt n) (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).X n) := by
  by_cases hn : (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n
  · have hn0 : n=0 := by
      cases n with
      | zero => rfl
      | succ n => exact False.elim ((RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).not_boundaryGE_next
          (show (ComplexShape.up ℕ).Rel n (n+1) from rfl) hn)
    subst n
    have := rationalFlasque_opcycles_of_exact_below K hK k he k le_rfl
    exact rationalSheafFlasque_of_iso (K.truncGE'XIsoOpcycles
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) (i' := k) rfl hn).symm
  · have := hK (k+n)
    exact rationalSheafFlasque_of_iso (K.truncGE'XIso (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn).symm

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularThomGoodShift_isFlasque (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).X n) :=
  rationalGoodShift_isFlasque Z.regularThomSheafComplex
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen)
    (2*p) (fun i hi => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z i (by omega)) n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions
