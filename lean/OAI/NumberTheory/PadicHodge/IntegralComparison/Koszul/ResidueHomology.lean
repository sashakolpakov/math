import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation
import Mathlib.Algebra.Homology.SingleHomology

/-! # Residue Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResidueHomology

noncomputable section

/-! The cochain residue obtained by evaluation on the ordered normal
wedge induces the original oriented top-Koszul cohomology isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] {c : ℕ} (s : Fin c → R)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology

def evaluation : (OrientedTopCohomology.dualComplex R s).X c ⟶ ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s) :=
  ModuleCat.ofHom ((OrientedTopCohomology.ideal R s).mkQ.comp (OrientedTopCohomology.evaluation R s).toLinearMap)

theorem boundary (i : ℕ) (hi : (ComplexShape.up ℕ).Rel i c) :
    (OrientedTopCohomology.dualComplex R s).d i c ≫ evaluation R s = 0 := by
  obtain rfl : c = i + 1 := hi.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Submodule.Quotient.mk
    (OrientedTopCohomology.evaluation R s ((OrientedTopCohomology.dualComplex R s).d i (i+1) x)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← OrientedTopCohomology.incoming_range R s]
  refine Submodule.mem_map.mpr ⟨(OrientedTopCohomology.dualComplex R s).d i (i+1) x, ?_, rfl⟩
  rw [CochainComplex.prev_nat_succ]
  exact ⟨x, rfl⟩

def map : OrientedTopCohomology.dualComplex R s ⟶
    (single (ModuleCat R) (.up ℕ) c).obj (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s)) :=
  mkHomToSingle (evaluation R s) (boundary R s)

theorem map_top : (map R s).f c ≫
    (singleObjXSelf (.up ℕ) c (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s))).hom = evaluation R s := by
  dsimp only [map]
  erw [mkHomToSingle_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem single_cycleClass {D : Type*} [Category D] [Abelian D]
    (N : D) (n : ℕ)
    (hz : IsZero (((single D (.up ℕ) n).obj N).X ((ComplexShape.up ℕ).next n))) :
    TopHomologyCokernel.cycleClass ((single D (.up ℕ) n).obj N) n hz ≫
      (singleObjHomologySelfIso (.up ℕ) n N).hom = (singleObjXSelf (.up ℕ) n N).hom := by
  dsimp only [TopHomologyCokernel.cycleClass, TopHomologyCokernel.shortClass]
  erw [Category.assoc, homologyπ_singleObjHomologySelfIso_hom]
  erw [← Category.assoc, ShortComplex.cyclesIsoX₂_inv_hom_id, Category.id_comp]

theorem homology : homologyMap (map R s) c ≫
    (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s))).hom =
      (OrientedTopCohomology.iso R s).hom := by
  let z := TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex R s) c (OrientedTopCohomology.outgoing_isZero R s)
  let : Epi z := by
    dsimp [z, TopHomologyCokernel.cycleClass, TopHomologyCokernel.shortClass]
    infer_instance
  let hz := isZero_single_obj_X (.up ℕ) c (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s))
    ((ComplexShape.up ℕ).next c) (by simp)
  apply (cancel_epi z).mp
  dsimp only [z]
  rw [← Category.assoc,
    DeterminantTransition.cycleClass_naturality (map R s) c (OrientedTopCohomology.outgoing_isZero R s) hz,
    Category.assoc, single_cycleClass, map_top, OrientedTopCohomology.cycleClass_iso]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResidueHomology
