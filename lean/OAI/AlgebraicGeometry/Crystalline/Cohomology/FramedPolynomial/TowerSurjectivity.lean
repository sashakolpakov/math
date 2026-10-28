import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.StructureSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PDInverseLimitExact

/-! # Tower Surjectivity -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerSurjectivity.FramedPolynomialTowerSurjectivity

noncomputable section

/-!
# Surjective section transitions on the actual framed polynomial tower

The envelope levels are subterminal framed objects, so injective sheaves
restrict surjectively along the tower. For the original structure sheaf,
surjectivity follows instead from the actual p-power quotient maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ (fun i => r (MvPolynomial.X i))
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B (MvPolynomial σ W) r hr hbase
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.functions p k B σ r hr hbase
local notation "Env" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W (MvPolynomial σ W) (Ideal.span {(p : W)})
  (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (RingHom.ker r)

local instance envelopeBaseAlgebra : Algebra W Env :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W (MvPolynomial σ W) (Ideal.span {(p : W)})
    (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (RingHom.ker r)).comp
      (algebraMap W (MvPolynomial σ W))).toAlgebra

instance transition_mono {n m : ℕ} (h : n ≤ m) : Mono ((T).map (homOfLE h)) where
  right_cancellation {P} f g _ :=
    @Subsingleton.elim _ (Universal.FramedPolynomialUniversal.hom_subsingleton p k B σ r hr hbase P n) f g

theorem injective_surjective (I : Sheaf K V) [Injective I] {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (I.obj.map ((T).map (homOfLE h)).op) := by
  intro x
  let a : ModuleCat.of (Site.CoefficientRing p k) (Site.CoefficientRing p k) ⟶
      I.obj.obj (op ((T).obj n)) := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  obtain ⟨b, hb⟩ := SheafInjective.SheafInjectiveRestrictions.exists_extension K ((T).map (homOfLE h))
    (ModuleCat.of (Site.CoefficientRing p k) (Site.CoefficientRing p k)) I a
  exact ⟨b 1, (congrArg (fun g => g 1) hb).trans (LinearMap.toSpanSingleton_apply_one _ _ x)⟩

theorem functions_epi {n m : ℕ} (h : n ≤ m) : Epi ((F).map (homOfLE h).op) := by
  let G := D ⋙ PD.InverseLimitUniversal.PDInverseLimitUniversal.ambientModules p k B
  have : Epi (G.map (homOfLE h).op) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact PDInverseLimitExact.PadicPDInverseLimitExact.transition_surjective p k B _ _ _ _ _ _ n m h
  let e := TowerDiagram.FramedPolynomialTowerDiagram.diagramIso p k B σ r hr hbase
  rw [← NatIso.naturality_1 e.symm (homOfLE h).op]
  infer_instance

theorem structure_surjective {n m : ℕ} (h : n ≤ m) :
    Function.Surjective ((StructureSections.FramedPolynomialStructureSections.structureSheaf p k B σ r).obj.map
      ((T).map (homOfLE h)).op) := by
  apply (ModuleCat.epi_iff_surjective _).mp
  have : Epi ((F).map (homOfLE h).op) := functions_epi p k B σ r hr hbase h
  have : Epi ((F ⋙ E).map (homOfLE h).op) := by
    change Epi ((E).map ((F).map (homOfLE h).op))
    infer_instance
  let e := StructureSections.FramedPolynomialStructureSections.towerSectionsIso p k B σ r hr hbase
  change Epi (((T).op ⋙ (StructureSections.FramedPolynomialStructureSections.structureSheaf p k B σ r).obj).map
    (homOfLE h).op)
  rw [← NatIso.naturality_1 e.symm (homOfLE h).op]
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerSurjectivity.FramedPolynomialTowerSurjectivity
