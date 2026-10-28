import OAI.AlgebraicGeometry.Cycles.Functoriality.UnitCap
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Support Map -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.SupportMap.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The underlying morphism with the carriers made explicit. -/
def algebraicMap {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver) :
    X.carrier ⟶ Y.carrier := f.left

theorem algebraicMap_over {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) : algebraicMap f ≫ Y.structureMap = X.structureMap := f.w

theorem supportMap_imageClosure {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    CycleClass.Geometric.StratumClosure.integralImageClosure (Z.inclusion ≫ algebraicMap f) = UnitCap.imageSupport f Z := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (algebraicMap f ∘ Z.inclusion)) = _
  rw [Set.range_comp, show Set.range Z.inclusion = (Z.1 : Set X.carrier) from
    CycleClass.Geometric.GenericPoint.range_reducedSupportι Z.1]
  have h : algebraicMap f '' (Z.1 : Set X.carrier) =
      (UnitCap.imageSupport f Z : Set Y.carrier) := (UnitCap.imageSupport_eq_image f hf Z).symm
  rw [h]
  exact (UnitCap.imageSupport f Z).isClosed.closure_eq

theorem supportMap_kernel {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    (Z.inclusion ≫ algebraicMap f).ker = CycleClass.Geometric.GenericPoint.reducedSupportIdeal (UnitCap.imageSupport f Z) := by
  let : IsProper (algebraicMap f) := hf
  exact (CycleClass.Geometric.StratumClosure.kernel_eq_reducedImageClosureIdeal (Z.inclusion ≫ algebraicMap f)).trans
    (congrArg CycleClass.Geometric.GenericPoint.reducedSupportIdeal (supportMap_imageClosure f hf Z))

/-- The genuine morphism from a reduced support to the reduced image support. -/
def supportImageMap {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    Z.scheme ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme (UnitCap.imageSupport f Z) := by
  apply IsClosedImmersion.lift (CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z))
    (Z.inclusion ≫ algebraicMap f)
  change (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (UnitCap.imageSupport f Z)).subschemeι.ker ≤ _
  rw [Scheme.IdealSheafData.ker_subschemeι, supportMap_kernel f hf Z]

theorem supportImageMap_inclusion {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    supportImageMap f hf Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z) =
      Z.inclusion ≫ algebraicMap f := by
  exact IsClosedImmersion.lift_fac (CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z))
    (Z.inclusion ≫ algebraicMap f) _

theorem supportImageMap_over {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    supportImageMap f hf Z ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap (UnitCap.imageSupport f Z) Y.structureMap =
      Z.structureMap := by
  change supportImageMap f hf Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z) ≫ Y.structureMap =
    Z.inclusion ≫ X.structureMap
  rw [← Category.assoc, supportImageMap_inclusion, Category.assoc, algebraicMap_over]

theorem supportImageMap_isProper {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    IsProper (supportImageMap f hf Z) := by
  let : IsProper (algebraicMap f) := hf
  let : IsProper (supportImageMap f hf Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z)) := by
    rw [supportImageMap_inclusion]
    infer_instance
  exact IsProper.of_comp (supportImageMap f hf Z) (CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z))

theorem supportImageMap_surjective {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    Function.Surjective (supportImageMap f hf Z) := by
  intro y
  have hy : CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z) y ∈ (UnitCap.imageSupport f Z : Set Y.carrier) := by
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact ⟨y, rfl⟩
  rw [UnitCap.imageSupport_eq_image f hf Z] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι Z.1] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨z, (CycleClass.Geometric.GenericPoint.reducedSupportι (UnitCap.imageSupport f Z)).isClosedEmbedding.injective ?_⟩
  have h := congrArg (fun k : Z.scheme ⟶ Y.carrier => k z)
    (supportImageMap_inclusion f hf Z)
  exact h.trans hxy

/-- Surjectivity sends the generic point to the generic point. -/
theorem genericPoint_eq_of_surjective {S T : Scheme} [IrreducibleSpace S]
    [IrreducibleSpace T] (f : S ⟶ T) (hf : Function.Surjective f) :
    f (genericPoint S) = genericPoint T := by
  apply IsGenericPoint.eq _ (genericPoint_spec T)
  have h := (genericPoint_spec S).image f.continuous
  simpa only [Set.image_univ, hf.range_eq, closure_univ] using h

theorem supportImageMap_genericPoint {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    supportImageMap f hf Z (genericPoint Z.scheme) =
      genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (UnitCap.imageSupport f Z)) :=
  genericPoint_eq_of_surjective _ (supportImageMap_surjective f hf Z)

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.SupportMap.Construction
