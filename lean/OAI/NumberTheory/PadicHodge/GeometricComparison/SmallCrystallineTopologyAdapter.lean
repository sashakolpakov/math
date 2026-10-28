import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Small Crystalline Topology Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineTopologyAdapter.SmallCrystallineAdapter

noncomputable section

/-! The crystalline category equivalence respects the ambient Zariski topologies. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

universe u
variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
  {X : Over (Spec (CommRingCat.of k))}

def unitNatIso : 𝟭 (SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) ≅ SmallCrystallineDpow.SmallCrystallineAdapter.to65 ⋙ SmallCrystallineDpow.SmallCrystallineAdapter.to62 :=
  NatIso.ofComponents SmallCrystallineEquivalence.SmallCrystallineAdapter.unitIso (by
    intro S T f
    apply AlgebraicGeometry.Crystalline.Cohomology.Site.Object.Hom.ext
    · apply AlgHom.ext
      intro x
      change T.thickening.ring ⧸ RingHom.ker T.thickening.reduction at x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (f.reduction_comm a).symm
    · rfl)

instance to65IsEquivalence : (SmallCrystallineDpow.SmallCrystallineAdapter.to65 (p := p) (k := k) (X := X)).IsEquivalence := by
  have : (SmallCrystallineDpow.SmallCrystallineAdapter.to65 (p := p) (k := k) (X := X) ⋙ SmallCrystallineDpow.SmallCrystallineAdapter.to62).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso unitNatIso).mp inferInstance
  exact Functor.isEquivalence_of_comp_right SmallCrystallineDpow.SmallCrystallineAdapter.to65 SmallCrystallineDpow.SmallCrystallineAdapter.to62

def explicitEquivalence : SmallCrystallineDpow.SmallCrystallineAdapter.Small65 (p := p) (k := k) (X := X) ≌ SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X) :=
  SmallCrystallineEquivalence.SmallCrystallineAdapter.equivalence.changeInverse
    (Functor.fullyFaithfulCancelRight SmallCrystallineDpow.SmallCrystallineAdapter.to62
      (SmallCrystallineEquivalence.SmallCrystallineAdapter.equivalence.counitIso ≪≫ unitNatIso))

theorem to62_ambient : SmallCrystallineDpow.SmallCrystallineAdapter.to62 (p := p) (k := k) (X := X) ⋙
    AlgebraicGeometry.Crystalline.Cohomology.Site.ambient p k X = IntegralComparison.Crystalline.Site.AffineThickening.ambient := rfl

theorem to65_ambient : SmallCrystallineDpow.SmallCrystallineAdapter.to65 (p := p) (k := k) (X := X) ⋙
    IntegralComparison.Crystalline.Site.AffineThickening.ambient = AlgebraicGeometry.Crystalline.Cohomology.Site.ambient p k X := rfl

theorem to62_precoverage : (AlgebraicGeometry.Crystalline.Cohomology.Site.precoverage p k X).comap SmallCrystallineDpow.SmallCrystallineAdapter.to62 =
    IntegralComparison.Crystalline.Site.AffineThickening.precoverage (p := p)
      (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (f := IntegralComparison.Witt.Crystalline.wittStructureMap p k X) := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.Site.precoverage, ← Precoverage.comap_comp, to62_ambient]
  rfl

theorem to65_precoverage :
    (IntegralComparison.Crystalline.Site.AffineThickening.precoverage (p := p)
      (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (f := IntegralComparison.Witt.Crystalline.wittStructureMap p k X)).comap SmallCrystallineDpow.SmallCrystallineAdapter.to65 =
    AlgebraicGeometry.Crystalline.Cohomology.Site.precoverage p k X := by
  rw [IntegralComparison.Crystalline.Site.AffineThickening.precoverage, ← Precoverage.comap_comp, to65_ambient]
  rfl

theorem continuous_of_precoverage_equivalence {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.IsEquivalence] (J : Precoverage C) (K : Precoverage D)
    (h : J ≤ K.comap F) : F.IsContinuous J.toGrothendieck K.toGrothendieck := by
  apply Functor.le_inducedTopology_iff.mp
  rw [J.toGrothendieck_eq_sInf]
  apply sInf_le
  intro U R hR
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  rw [← Sieve.generate_map_eq_functorPushforward]
  exact Precoverage.generate_mem_toGrothendieck (h _ hR)

abbrev topology62 := AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
abbrev topology65 := IntegralComparison.Crystalline.Site.AffineThickening.topology (p := p)
  (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (f := IntegralComparison.Witt.Crystalline.wittStructureMap p k X)

instance to62Continuous : (SmallCrystallineDpow.SmallCrystallineAdapter.to62 (p := p) (k := k) (X := X)).IsContinuous topology65 topology62 :=
  continuous_of_precoverage_equivalence SmallCrystallineDpow.SmallCrystallineAdapter.to62 _ _ to62_precoverage.ge

instance to65Continuous : (SmallCrystallineDpow.SmallCrystallineAdapter.to65 (p := p) (k := k) (X := X)).IsContinuous topology62 topology65 :=
  continuous_of_precoverage_equivalence SmallCrystallineDpow.SmallCrystallineAdapter.to65 _ _ to65_precoverage.ge

def continuousSheafEquivalence {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    (A : Type*) [Category* A] [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J] :
    Sheaf J A ≌ Sheaf K A where
  functor := e.inverse.sheafPushforwardContinuous A K J
  inverse := e.functor.sheafPushforwardContinuous A J K
  unitIso := NatIso.ofComponents (fun F =>
    ObjectProperty.isoMk _ (isoWhiskerRight e.op.unitIso F.obj))
    (fun {F G} α => by
      ext U
      exact (α.hom.naturality (e.op.unitIso.hom.app U)).symm)
  counitIso := NatIso.ofComponents (fun F =>
    ObjectProperty.isoMk _ (isoWhiskerRight e.op.counitIso F.obj))
    (fun {F G} α => by
      ext U
      exact (α.hom.naturality (e.op.counitIso.hom.app U)).symm)
  functor_unitIso_comp F := by
    ext U
    change F.obj.map (e.op.unitIso.hom.app (e.op.inverse.obj U)) ≫
      F.obj.map (e.op.inverse.map (e.op.counitIso.hom.app U)) = 𝟙 _
    rw [← Functor.map_comp, Equivalence.unit_inverse_comp]
    exact F.obj.map_id _

instance explicitContinuous :
    (explicitEquivalence (p := p) (k := k) (X := X)).functor.IsContinuous topology65 topology62 :=
  to62Continuous

instance explicitInverseContinuous :
    (explicitEquivalence (p := p) (k := k) (X := X)).inverse.IsContinuous topology62 topology65 :=
  to65Continuous

def sheafEquivalence (A : Type*) [Category* A] :
    Sheaf (topology65 (p := p) (k := k) (X := X)) A ≌
      Sheaf (topology62 (p := p) (k := k) (X := X)) A :=
  continuousSheafEquivalence topology65 topology62 explicitEquivalence A

instance to65Cocontinuous : (SmallCrystallineDpow.SmallCrystallineAdapter.to65 (p := p) (k := k) (X := X)).IsCocontinuous topology62 topology65 :=
  (explicitEquivalence.symm.toAdjunction.isCocontinuous_iff_coverPreserving topology62 topology65).mpr
    (CoverPreserving.of_isContinuous SmallCrystallineDpow.SmallCrystallineAdapter.to62 topology65 topology62)

instance to62Cocontinuous : (SmallCrystallineDpow.SmallCrystallineAdapter.to62 (p := p) (k := k) (X := X)).IsCocontinuous topology65 topology62 :=
  (explicitEquivalence.toAdjunction.isCocontinuous_iff_coverPreserving topology65 topology62).mpr
    (CoverPreserving.of_isContinuous SmallCrystallineDpow.SmallCrystallineAdapter.to65 topology62 topology65)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineTopologyAdapter.SmallCrystallineAdapter
