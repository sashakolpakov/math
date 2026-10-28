import OAI.AlgebraicGeometry.ComplexMultiplication.HomologyFunctorCoherence
import OAI.Algebra.Homology.MapExtend
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Scalar Extend Homology Coherence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ScalarExtendHomologyCoherence

noncomputable section

/-! # Exact coefficient functors commute with the canonical extension homology isomorphism -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory Limits _root_.HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (K : CochainComplex C ℕ) (n : ℕ)
local notation "e" => ComplexShape.embeddingUpNat
local notation "KN" => Functor.obj (F.mapHomologicalComplex (ComplexShape.up ℕ)) K
local notation "KI" => Functor.obj (F.mapHomologicalComplex (ComplexShape.up ℤ)) (K.extend (e))

theorem scalarExtendCyclesCoherence :
    cyclesMap (OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K (e)).hom ((e).f n) ≫
      ((KN).extendCyclesIso (e) rfl).hom ≫ ((K.sc n).mapCyclesIso F).hom =
    (((K.extend (e)).sc ((e).f n)).mapCyclesIso F).hom ≫
      F.map (K.extendCyclesIso (e) rfl).hom := by
  apply (cancel_mono (F.map (K.iCycles n))).mp
  have hN : ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.iCycles n) = (KN).iCycles n :=
    ShortComplex.mapCyclesIso_hom_iCycles (K.sc n) F
  have hI : (((K.extend (e)).sc ((e).f n)).mapCyclesIso F).hom ≫
      F.map ((K.extend (e)).iCycles ((e).f n)) = (KI).iCycles ((e).f n) :=
    ShortComplex.mapCyclesIso_hom_iCycles ((K.extend (e)).sc ((e).f n)) F
  simp only [Category.assoc]
  rw [hN, HomologicalComplex.extendCyclesIso_hom_iCycles]
  rw [← F.map_comp, HomologicalComplex.extendCyclesIso_hom_iCycles, F.map_comp]
  rw [← Category.assoc (((K.extend (e)).sc ((e).f n)).mapCyclesIso F).hom,
    hI, HomologicalComplex.cyclesMap_i_assoc,
    OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_hom_f F K (e) rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem scalarExtendHomologyCoherence :
    homologyMap (OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K (e)).hom ((e).f n) ≫
      ((KN).extendHomologyIso (e) rfl).hom ≫ ((K.sc n).mapHomologyIso F).hom =
    (((K.extend (e)).sc ((e).f n)).mapHomologyIso F).hom ≫
      F.map (K.extendHomologyIso (e) rfl).hom := by
  apply (cancel_epi ((KI).homologyπ ((e).f n))).mp
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom_assoc]
  have hN := HomologyFunctorCoherence.homologyComparison_cycles (K.sc n) F
  have hI := HomologyFunctorCoherence.homologyComparison_cycles ((K.extend (e)).sc ((e).f n)) F
  change (KN).homologyπ n ≫ ((K.sc n).mapHomologyIso F).hom =
    ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) at hN
  change (KI).homologyπ ((e).f n) ≫
    (((K.extend (e)).sc ((e).f n)).mapHomologyIso F).hom =
    (((K.extend (e)).sc ((e).f n)).mapCyclesIso F).hom ≫
      F.map ((K.extend (e)).homologyπ ((e).f n)) at hI
  rw [hN, ← Category.assoc ((KI).homologyπ ((e).f n)), hI]
  simp only [Category.assoc, ← F.map_comp]
  rw [HomologicalComplex.homologyπ_extendHomologyIso_hom, F.map_comp]
  simpa only [Category.assoc] using! congrArg (fun f => f ≫ F.map (K.homologyπ n))
    (scalarExtendCyclesCoherence F K n)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ScalarExtendHomologyCoherence
