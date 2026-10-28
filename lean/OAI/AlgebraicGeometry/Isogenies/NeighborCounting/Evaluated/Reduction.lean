import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Targets

/-! # Reduction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated

noncomputable section

/-! Reduction of independently evaluated targets to native geometric PEL
points. The map is constructed by the special-fiber pullback square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable (b : B.R →+* R)
variable (residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

theorem Reduction.Lifts.residueCompatible_geometric_square
    (hbase : Lifts.ResidueCompatible D R b residueIso) :
    Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ Lifts.closedBase R ≫ Lifts.dvrBase R b =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom ≫ D.specialBase := by
  change Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ Spec.map (CommRingCat.ofHom b) =
    Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) ≫
      Spec.map (CommRingCat.ofHom D.residue)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  have ha := RingHom.congr_fun hbase a
  exact (congrArg residueIso.symm ha).trans (residueIso.symm_apply_apply _)

section

variable {D R L b} (z : Targets.Lifts.EvaluatedTarget D R L b)
variable {residueIso} (hbase : Lifts.ResidueCompatible D R b residueIso)

/-- The independently extended target determines an actual geometric point
of the special moduli scheme, without a target-identification hypothesis. -/
def Targets.Lifts.EvaluatedTarget.specialPoint : D.GeometricPoint :=
  Over.homMk
    (pullback.lift
      (Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ z.reduction)
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom (by
        erw [Category.assoc]
        change Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
          (Lifts.closedBase R ≫ z.extension) ≫ D.integral.toOver.hom = _
        rw [Category.assoc, z.extension_overBase]
        exact Reduction.Lifts.residueCompatible_geometric_square D R b residueIso hbase))
    (pullback.lift_snd _ _ _)

theorem Targets.Lifts.EvaluatedTarget.specialPoint_projection :
    (z.specialPoint hbase).left ≫ D.specialProjection =
      Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ z.reduction :=
  pullback.lift_fst _ _ _

/-- The full polarized fiber of the reduction is the pullback at the
constructed geometric moduli point. -/
def Targets.Lifts.EvaluatedTarget.geometricPolarizedIso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    ((D.integral.universal.data.polarized.pullback z.reduction).pullback
      (Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom)))
    (D.integral.universal.data.polarized.pullback
      ((z.specialPoint hbase).left ≫ D.specialProjection)) := by
  have e := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp D.integral.universal.data.polarized
    z.reduction (Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom))
  rw [← z.specialPoint_projection hbase] at e
  exact e

variable (D R L b) in
def Targets.Lifts.EvaluatedTarget.ofIntegralMap (a : Spec (.of R) ⟶ D.integral.toOver.left)
    (ha : a ≫ D.integral.toOver.hom = Lifts.dvrBase R b) : Targets.Lifts.EvaluatedTarget D R L b where
  map := Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ a
  overBase := by rw [Category.assoc, ha]

theorem Targets.Lifts.EvaluatedTarget.extension_ofIntegralMap (a : Spec (.of R) ⟶ D.integral.toOver.left)
    (ha : a ≫ D.integral.toOver.hom = Lifts.dvrBase R b) :
    (Targets.Lifts.EvaluatedTarget.ofIntegralMap D R L b a ha).extension = a :=
  ((Targets.Lifts.EvaluatedTarget.ofIntegralMap D R L b a ha).extension_unique a rfl ha).symm

end

/-- Reduce a generic target multiset to the native geometric PEL points;
duplicate special points remain duplicate entries. -/
def Reduction.Lifts.reduceToGeometricPoints (hbase : Lifts.ResidueCompatible D R b residueIso)
    (neighbors : Multiset (Targets.Lifts.EvaluatedTarget D R L b)) : Multiset D.GeometricPoint :=
  neighbors.map (fun z => z.specialPoint hbase)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated
