import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Reduction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection

/-! # Evaluated Target Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedTargetBaseChange.CM

noncomputable section

/-! Properly evaluated NeighborCounting targets extend along a DVR embedding.
Their generic maps are the original maps under field extension, and
compatible residue maps preserve the original special target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Reduction.Lifts

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} (z : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget D R L b)

def changeBase {b' : B.R →+* R} (hb : b = b') : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget D R L b' := hb ▸ z

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L] in
theorem changeBase_map {b' : B.R →+* R} (hb : b = b') :
    (changeBase z hb).map = z.map := by
  subst b'
  rfl

theorem changeBase_specialPoint {b' : B.R →+* R} (hb : b = b')
    (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
    (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ) (hbase' : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b' ρ) :
    (changeBase z hb).specialPoint hbase' = z.specialPoint hbase := by
  subst b'
  rfl

variable {R' L' : Type} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
  [Field L'] [Algebra R' L'] [IsFractionRing R' L']
  (φ : R →+* R') (σ : L →+* L')
  (hfrac : (algebraMap R' L').comp φ = σ.comp (algebraMap R L))

def integralMap : Spec (.of R') ⟶ D.integral.toOver.left :=
  Spec.map (CommRingCat.ofHom φ) ≫ z.extension

omit [IsDomain R'] [IsDiscreteValuationRing R'] in
theorem integralMap_base : integralMap z φ ≫ D.integral.toOver.hom = Isogenies.NeighborCounting.Lifts.dvrBase R' (φ.comp b) := by
  change (Spec.map (CommRingCat.ofHom φ) ≫ z.extension) ≫ _ = _
  rw [Category.assoc, z.extension_overBase]
  exact (Spec.map_comp (CommRingCat.ofHom b) (CommRingCat.ofHom φ)).symm

def target : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget D R' L' (φ.comp b) :=
  Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget.ofIntegralMap D R' L' (φ.comp b) (integralMap z φ) (integralMap_base z φ)

theorem target_extension : (target (L' := L') z φ).extension = integralMap z φ :=
  Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget.extension_ofIntegralMap (integralMap z φ) (integralMap_base z φ)

include hfrac in
omit [IsFractionRing R' L'] [IsDomain R'] [IsDiscreteValuationRing R'] in
theorem target_map : (target (L' := L') z φ).map = Spec.map (CommRingCat.ofHom σ) ≫ z.map := by
  have hs : Spec.map (CommRingCat.ofHom (algebraMap R' L')) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : R →+* L' => Spec.map (CommRingCat.ofHom f)) hfrac
  change Spec.map (CommRingCat.ofHom (algebraMap R' L')) ≫
    (Spec.map (CommRingCat.ofHom φ) ≫ z.extension) = _
  rw [← Category.assoc, hs, Category.assoc, z.extension_generic]

variable (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
  (ρ' : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R')
  (hres : ∀ r, ρ'.symm (IsLocalRing.residue R' (φ r)) = ρ.symm (IsLocalRing.residue R r))
  (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ)

include hres hbase in
theorem residueCompatible : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R' (φ.comp b) ρ' := by
  ext a
  apply ρ'.symm.injective
  exact (hres (b a)).trans
    ((congrArg ρ.symm (RingHom.congr_fun hbase a)).trans
      ((ρ.symm_apply_apply _).trans (ρ'.symm_apply_apply _).symm))

include hres in
theorem specialPoint_eq (hbase' : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R' (φ.comp b) ρ') :
    (target (L' := L') z φ).specialPoint hbase' = z.specialPoint hbase := by
  apply ReductionPointProjection.CM.Recovery.point_eq_of_projection D.specialBase D.integral.toOver
    (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)
  refine ((target (L' := L') z φ).specialPoint_projection hbase').trans ?_
  refine Eq.trans ?_ (z.specialPoint_projection hbase).symm
  have hs : (Spec.map (CommRingCat.ofHom ρ'.symm.toRingHom) ≫ Isogenies.NeighborCounting.Lifts.closedBase R') ≫
      Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ρ.symm.toRingHom) ≫ Isogenies.NeighborCounting.Lifts.closedBase R := by
    change (Spec.map (CommRingCat.ofHom ρ'.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R'))) ≫ Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom ρ.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : R →+* AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q => Spec.map (CommRingCat.ofHom f)) (RingHom.ext hres)
  change Spec.map (CommRingCat.ofHom ρ'.symm.toRingHom) ≫
      (Isogenies.NeighborCounting.Lifts.closedBase R' ≫ (target (L' := L') z φ).extension) =
    Spec.map (CommRingCat.ofHom ρ.symm.toRingHom) ≫ (Isogenies.NeighborCounting.Lifts.closedBase R ≫ z.extension)
  rw [target_extension]
  change Spec.map (CommRingCat.ofHom ρ'.symm.toRingHom) ≫
      (Isogenies.NeighborCounting.Lifts.closedBase R' ≫ (Spec.map (CommRingCat.ofHom φ) ≫ z.extension)) = _
  simpa only [Category.assoc] using congrArg (· ≫ z.extension) hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedTargetBaseChange.CM
