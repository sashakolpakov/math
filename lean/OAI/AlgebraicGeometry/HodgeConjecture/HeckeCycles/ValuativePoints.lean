import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Targets
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula

/-! # Valuative Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM

noncomputable section

/-! Properness gives a canonical specialization of evaluated generic
points. On a proper group this is an additive map, so every actual
pointwise Hecke sum specializes with all its multiplicities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {S : Scheme} (b : Spec (.of R) ⟶ S)

def genericBase : Spec (.of L) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R L))

def genericTest : Over S := Over.mk (genericBase (R := R) (L := L) ≫ b)

def restrictTest : genericTest (L := L) b ⟶ Over.mk b :=
  Over.homMk (genericBase (R := R) (L := L)) rfl

def restrictPoint (X : Over S) : (Over.mk b ⟶ X) → (genericTest (L := L) b ⟶ X) :=
  fun x => restrictTest b ≫ x

theorem restrictPoint_bijective (X : Over S) [IsProper X.hom] :
    Function.Bijective (restrictPoint (L := L) b X) := by
  constructor
  · intro x y h
    have hz : (restrictPoint (L := L) b X x).left ≫ X.hom =
        genericBase (R := R) (L := L) ≫ b := (restrictPoint (L := L) b X x).w
    obtain ⟨z, _, hu⟩ := Isogenies.NeighborCounting.Evaluated.Targets.Lifts.proper_evaluated_extension
      X.hom b (restrictPoint (L := L) b X x).left hz
    apply Over.OverMorphism.ext
    exact (hu x.left ⟨rfl, x.w⟩).trans
      (hu y.left ⟨congrArg (fun t : genericTest (L := L) b ⟶ X => t.left) h.symm,
        y.w⟩).symm
  · intro z
    obtain ⟨x, hx, _⟩ := Isogenies.NeighborCounting.Evaluated.Targets.Lifts.proper_evaluated_extension X.hom b z.left z.w
    exact ⟨Over.homMk x hx.2, Over.OverMorphism.ext hx.1⟩

def evaluatedPointEquiv (X : Over S) [IsProper X.hom] :
    (Over.mk b ⟶ X) ≃ (genericTest (L := L) b ⟶ X) :=
  Equiv.ofBijective (restrictPoint b X) (restrictPoint_bijective b X)

theorem extendPoint_map {X Y : Over S} [IsProper X.hom] [IsProper Y.hom]
    (a : X ⟶ Y) (z : genericTest (L := L) b ⟶ X) :
    (evaluatedPointEquiv b Y).symm (z ≫ a) = (evaluatedPointEquiv b X).symm z ≫ a := by
  apply (evaluatedPointEquiv (L := L) b Y).injective
  rw [Equiv.apply_symm_apply]
  change z ≫ a = restrictTest b ≫ ((evaluatedPointEquiv b X).symm z ≫ a)
  rw [← Category.assoc]
  exact congrArg (· ≫ a) ((evaluatedPointEquiv b X).apply_symm_apply z).symm

variable (G : CommGrp (Over S)) [IsProper G.X.hom]

def evaluatedGroupEquiv :
    Additive (Over.mk b ⟶ G.X) ≃+ Additive (genericTest (L := L) b ⟶ G.X) where
  toFun x := Additive.ofMul (evaluatedPointEquiv b G.X x.toMul)
  invFun x := Additive.ofMul ((evaluatedPointEquiv b G.X).symm x.toMul)
  left_inv x := congrArg Additive.ofMul ((evaluatedPointEquiv b G.X).symm_apply_apply x.toMul)
  right_inv x := congrArg Additive.ofMul ((evaluatedPointEquiv b G.X).apply_symm_apply x.toMul)
  map_add' x y := MonObj.comp_mul (restrictTest b) x.toMul y.toMul

variable {k : Type} [Field k] (res : R →+* k)

def specialTest : Over S := Over.mk (Spec.map (CommRingCat.ofHom res) ≫ b)

def reductionTest : specialTest b res ⟶ Over.mk b :=
  Over.homMk (Spec.map (CommRingCat.ofHom res)) rfl

def reduceIntegralGroup : Additive (Over.mk b ⟶ G.X) →+
    Additive (specialTest b res ⟶ G.X) where
  toFun x := Additive.ofMul (reductionTest b res ≫ x.toMul)
  map_zero' := by
    change reductionTest b res ≫ (1 : Over.mk b ⟶ G.X) = 1
    exact MonObj.comp_one _
  map_add' x y := MonObj.comp_mul _ x.toMul y.toMul

def specializeGroup : Additive (genericTest (L := L) b ⟶ G.X) →+
    Additive (specialTest b res ⟶ G.X) :=
  (reduceIntegralGroup b G res).comp (evaluatedGroupEquiv b G).symm.toAddMonoidHom

def specializePoint (X : Over S) [IsProper X.hom]
    (z : genericTest (L := L) b ⟶ X) : specialTest b res ⟶ X :=
  reductionTest b res ≫ (evaluatedPointEquiv b X).symm z

theorem specializeGroup_map {X : Over S} [IsProper X.hom]
    (a : X ⟶ G.X) (z : genericTest (L := L) b ⟶ X) :
    specializeGroup b G res (Additive.ofMul (z ≫ a)) =
      Additive.ofMul (specializePoint b res X z ≫ a) := by
  apply Additive.toMul.injective
  change reductionTest b res ≫ (evaluatedPointEquiv b G.X).symm (z ≫ a) = _
  rw [extendPoint_map]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM
