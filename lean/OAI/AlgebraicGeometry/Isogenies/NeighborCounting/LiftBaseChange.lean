import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationIntegersHenselian

/-! # Lift Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-!
Extend an actual DVRLifting lift through the constructed finite evaluation DVR.
The source point and arithmetic map are pulled back literally, and the
new reduction equation follows from the residue-ring comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
variable {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable (j : R →+* R') (ρ : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField R')
variable (hρ : ∀ r : R, ρ (IsLocalRing.residue R r) = IsLocalRing.residue R' (j r))

include hρ in
theorem LiftBaseChange.Lifts.closedBase_baseChange :
    Lifts.closedBase R' ≫ Spec.map (CommRingCat.ofHom j) =
      Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ Lifts.closedBase R := by
  change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R')) ≫ Spec.map (CommRingCat.ofHom j) =
    Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (hρ r).symm)

include hρ in
theorem LiftBaseChange.Lifts.residueCompatible_baseChange (hbase : Lifts.ResidueCompatible D R b residueIso) :
    Lifts.ResidueCompatible D R' (j.comp b) (residueIso.trans ρ) := by
  apply RingHom.ext
  intro r
  change IsLocalRing.residue R' (j (b r)) = ρ (residueIso _)
  rw [← hρ]
  exact congrArg ρ (RingHom.congr_fun hbase r)

variable {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

def Lifts.IntegralLift.baseChange : Lifts.IntegralLift D R' (j.comp b) (residueIso.trans ρ) x where
  map := Spec.map (CommRingCat.ofHom j) ≫ l.map
  overBase := by
    rw [Category.assoc, l.overBase]
    change Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (j.comp b))
    rw [← Spec.map_comp]
    rfl
  reduction := by
    rw [← Category.assoc, LiftBaseChange.Lifts.closedBase_baseChange j ρ hρ, Category.assoc, l.reduction]
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom residueIso.toRingHom) ≫ x.left ≫ D.specialProjection =
      Spec.map (CommRingCat.ofHom (residueIso.trans ρ).toRingHom) ≫ x.left ≫ D.specialProjection
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

theorem Lifts.IntegralLift.baseChange_map : (l.baseChange j ρ hρ).map = Spec.map (CommRingCat.ofHom j) ≫ l.map := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
