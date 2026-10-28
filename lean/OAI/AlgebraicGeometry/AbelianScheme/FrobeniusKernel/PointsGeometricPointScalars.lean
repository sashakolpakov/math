import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointLift

/-! # Points Geometric Point Scalars -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointScalars.Construction

noncomputable section

/-!
The constructed geometric residue-field comparison preserves the
actual prime-field scalar map and every CMPoints Lie character.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
variable (R : M.GoodIntegralReduction q j) (a : M.Family)
variable (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a)

theorem l45GeometricPointFieldIso_scalar :
    CommRingCat.ofHom (R.fiberScalar a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)) ≫
      (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom =
        CommRingCat.ofHom (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q)) := by
  let y := PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x
  let t := Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom
  let s := Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q)))
  have ht : (t ≫ R.fiberMap a y) ≫ (R.geometricFiber a).hom = 𝟙 _ :=
    (congrArg (fun z => z ≫ (R.geometricFiber a).hom)
      (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso_fiberMap M R a x)).trans
        (PointsGeometricPointLift.Construction.l45GeometricPointLift_section M R a x)
  apply Spec.map_injective
  rw [Spec.map_comp]
  change t ≫ Spec.map (Spec.preimage (R.fiberMap a y ≫ (R.geometricFiber a).hom ≫ s)) = s
  rw [Spec.map_preimage]
  exact (Category.assoc t (R.fiberMap a y) ((R.geometricFiber a).hom ≫ s)).symm.trans
    ((Category.assoc (t ≫ R.fiberMap a y) (R.geometricFiber a).hom s).symm.trans
      ((congrArg (fun z => z ≫ s) ht).trans (Category.id_comp s)))

/-- The Lie character after the field comparison is the original
q-adic character reduced into the fixed geometric field. -/
theorem l45GeometricPointFieldIso_lieCharacter (τ : Gal(E/ℚ)) :
    (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom.hom.comp
      (R.lieCharacter a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x) τ) =
    (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q)).comp
      (PadicInt.toZMod.comp (j.localCharacter M.extendedEmbedding τ)) := by
  apply RingHom.ext
  intro b
  exact congrArg (fun f : CommRingCat.of (ZMod q) ⟶ CommRingCat.of (ModuliPoint.Construction.residueClosure q) =>
    f (PadicInt.toZMod (j.localCharacter M.extendedEmbedding τ b)))
      (l45GeometricPointFieldIso_scalar M R a x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointScalars.Construction
