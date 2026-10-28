import OAI.AlgebraicGeometry.SmoothMorphisms.DVRLifting
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Lifts -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts

noncomputable section

/-!
Lift the actual geometric point of the native integral PEL model over a
compatible complete DVR. DVRLifting is applied to the genuine base change of the
smooth moduli scheme. The lifted polarized family and integral action are
then literal pullbacks of the universal data.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable (b : B.R →+* R)
variable (residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

def dvrBase : Spec (.of R) ⟶ B.base := Spec.map (CommRingCat.ofHom b)
def closedBase : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- Compatibility of the arithmetic DVR with the chosen geometric residue
field and residue map. This describes the base alone. -/
def ResidueCompatible : Prop :=
  (IsLocalRing.residue R).comp b = residueIso.toRingHom.comp
    ((algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)).comp D.residue)

def residuePoint (x : D.GeometricPoint) :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ D.integral.toOver.left :=
  Spec.map (CommRingCat.ofHom residueIso.toRingHom) ≫ x.left ≫ D.specialProjection

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
theorem residuePoint_square (hbase : ResidueCompatible D R b residueIso)
    (x : D.GeometricPoint) :
    residuePoint D R residueIso x ≫ D.integral.toOver.hom = closedBase R ≫ dvrBase R b := by
  change (Spec.map (CommRingCat.ofHom residueIso.toRingHom) ≫ x.left ≫
      pullback.fst D.integral.toOver.hom D.specialBase) ≫ D.integral.toOver.hom = _
  erw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x.left,
    x.w]
  change Spec.map (CommRingCat.ofHom residueIso.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) ≫
      Spec.map (CommRingCat.ofHom D.residue) =
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ Spec.map (CommRingCat.ofHom b)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext hbase.symm)

/-- A lift is an actual morphism into the integral moduli scheme, with
its arithmetic-base square and its prescribed reduction. -/
structure IntegralLift (x : D.GeometricPoint) where
  map : Spec (.of R) ⟶ D.integral.toOver.left
  overBase : map ≫ D.integral.toOver.hom = dvrBase R b
  reduction : closedBase R ≫ map = residuePoint D R residueIso x

theorem integralLift_exists (hbase : ResidueCompatible D R b residueIso)
    (x : D.GeometricPoint) : Nonempty (IntegralLift D R b residueIso x) := by
  let X := (Over.pullback (dvrBase R b)).obj D.integral.toOver
  have : Smooth X.hom := inferInstanceAs
    (Smooth (pullback.snd D.integral.toOver.hom (dvrBase R b)))
  let xR : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X.left :=
    pullback.lift (residuePoint D R residueIso x) (closedBase R)
      (residuePoint_square D R b residueIso hbase x)
  have hxR : xR ≫ X.hom = closedBase R := pullback.lift_snd _ _ _
  obtain ⟨l, hl, hred⟩ := SmoothMorphisms.DVRLifting.lift_special_fiber_point R X.left X.hom xR hxR
  refine ⟨⟨l ≫ pullback.fst D.integral.toOver.hom (dvrBase R b), ?_, ?_⟩⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (l ≫ X.hom) ≫ dvrBase R b = _
    rw [hl, Category.id_comp]
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ pullback.fst D.integral.toOver.hom (dvrBase R b)) hred).trans
        (pullback.lift_fst _ _ _))

def integralLift (hbase : ResidueCompatible D R b residueIso) (x : D.GeometricPoint) :
    IntegralLift D R b residueIso x := (integralLift_exists D R b residueIso hbase x).some

namespace IntegralLift

variable {D R b residueIso} {x : D.GeometricPoint}
variable (l : IntegralLift D R b residueIso x)

abbrev actionData :
    PELModuli.IntegralModel.PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N (Spec (.of R)) :=
  D.integral.universal.data.pullback l.map

abbrev polarized : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N (Spec (.of R)) :=
  l.actionData.polarized

abbrev action : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) l.polarized.abelian :=
  l.actionData.action

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
theorem specializes_to_point : closedBase R ≫ l.map = residuePoint D R residueIso x := l.reduction

end IntegralLift

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts
