import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure
import OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints

/-! # Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

noncomputable section

/-! The actual proper morphism from each integral cycle support to its
reduced image. Its residue degrees agree with the coefficients used by ProjectionFormula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}

def algebraicMap (f : X.toOver ⟶ Y.toOver) : X.carrier ⟶ Y.carrier := f.left

theorem imageClosure_eq (f : X.toOver ⟶ Y.toOver) (W : IrreducibleCloseds X.carrier) :
    CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ algebraicMap f) = ProperCycleLinearity.imageSupport f W := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (algebraicMap f ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W)) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  change closure (f.left '' (W : Set X.carrier)) = _
  rw [← ProperCycleLinearity.imageSupport_eq_image f W]
  exact (ProperCycleLinearity.imageSupport f W).isClosed.closure_eq

theorem supportMap_kernel (f : X.toOver ⟶ Y.toOver) (W : IrreducibleCloseds X.carrier) :
    (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ algebraicMap f).ker = CycleClass.Geometric.GenericPoint.reducedSupportIdeal (ProperCycleLinearity.imageSupport f W) := by
  let : IsProper (algebraicMap f) := ProperCycleLinearity.morphism_isProper f
  exact (CycleClass.Geometric.StratumClosure.kernel_eq_reducedImageClosureIdeal (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ algebraicMap f)).trans
    (congrArg CycleClass.Geometric.GenericPoint.reducedSupportIdeal (imageClosure_eq f W))

def supportImageMap (f : X.toOver ⟶ Y.toOver) (W : IrreducibleCloseds X.carrier) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W) := by
  apply IsClosedImmersion.lift (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W))
    (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ algebraicMap f)
  change (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (ProperCycleLinearity.imageSupport f W)).subschemeι.ker ≤ _
  rw [Scheme.IdealSheafData.ker_subschemeι, supportMap_kernel]

theorem supportImageMap_inclusion (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    supportImageMap f W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) =
      CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ algebraicMap f :=
  IsClosedImmersion.lift_fac (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W))
    (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ algebraicMap f) _

theorem supportImageMap_over (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    supportImageMap f W ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap := by
  change supportImageMap f W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) ≫ Y.structureMap =
    CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap
  rw [← Category.assoc, supportImageMap_inclusion, Category.assoc]
  exact congrArg (fun g => CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ g) f.w

instance supportImageMap_isProper (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) : IsProper (supportImageMap f W) := by
  let : IsProper (algebraicMap f) := ProperCycleLinearity.morphism_isProper f
  let : IsProper (supportImageMap f W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W)) := by
    rw [supportImageMap_inclusion]
    infer_instance
  exact IsProper.of_comp (supportImageMap f W) (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W))

theorem supportImageMap_surjective (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) : Function.Surjective (supportImageMap f W) := by
  intro y
  have hy : CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) y ∈ (ProperCycleLinearity.imageSupport f W : Set Y.carrier) := by
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact ⟨y, rfl⟩
  rw [ProperCycleLinearity.imageSupport_eq_image] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι W] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨z, (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W)).isClosedEmbedding.injective ?_⟩
  have h := congrArg (fun k : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ Y.carrier => k z)
    (supportImageMap_inclusion f W)
  exact h.trans hxy

theorem supportImageMap_genericPoint (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    supportImageMap f W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) =
      genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)) := by
  apply IsGenericPoint.eq _ (genericPoint_spec _)
  have h := (genericPoint_spec (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)).image
    (supportImageMap f W).continuous
  simpa only [Set.image_univ, (supportImageMap_surjective f W).range_eq,
    closure_univ] using h

theorem residueDegree_post_immersion {A B C : Scheme}
    (f : A ⟶ B) (i : B ⟶ C) [SurjectiveOnStalks i] (x : A) :
    (f ≫ i).residueDegree x = f.residueDegree x := by
  let : Algebra (C.residueField (i (f x))) (A.residueField x) :=
    ((f ≫ i).residueFieldMap x).hom.toAlgebra
  let : Algebra (B.residueField (f x)) (A.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv
    (Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks i (f x)).commRingCatIsoToRingEquiv
    (RingEquiv.refl (A.residueField x))
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f i x).symm

theorem residueDegree_pre_immersion {A B C : Scheme}
    (i : A ⟶ B) (f : B ⟶ C) [SurjectiveOnStalks i] (x : A) :
    (i ≫ f).residueDegree x = f.residueDegree (i x) := by
  let : Algebra (C.residueField (f (i x))) (B.residueField (i x)) :=
    (f.residueFieldMap (i x)).hom.toAlgebra
  let : Algebra (C.residueField (f (i x))) (A.residueField x) :=
    ((i ≫ f).residueFieldMap x).hom.toAlgebra
  symm
  apply Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.refl (C.residueField (f (i x))))
    (Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks i x).commRingCatIsoToRingEquiv
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp i f x)

/-- The morphism between reduced supports has exactly the ambient residue
degree at every point, including singular points of the supports. -/
theorem supportImageMap_residueDegree (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :
    (supportImageMap f W).residueDegree x =
      f.left.residueDegree (CycleClass.Geometric.GenericPoint.reducedSupportι W x) := by
  have h := congrArg
    (fun g : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ Y.carrier => g.residueDegree x)
    (supportImageMap_inclusion f W)
  rw [residueDegree_post_immersion, residueDegree_pre_immersion] at h
  exact h

theorem supportImageMap_generic_residueDegree (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    (supportImageMap f W).residueDegree (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) =
      f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W) := by
  rw [supportImageMap_residueDegree, CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq]
  rfl

/-- Proper pushforward factors through the actual integral-support map.
This equality retains all residue-field weights. -/
theorem pointPushforward_supportImageMap (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W))).comp
        (CyclePushforward.pointPushforward (supportImageMap f W)) =
      (CyclePushforward.pointPushforward (algebraicMap f)).comp
        (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W)) := by
  rw [← CyclePushforward.pointPushforward_comp,
    ← CyclePushforward.pointPushforward_comp, supportImageMap_inclusion]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map
