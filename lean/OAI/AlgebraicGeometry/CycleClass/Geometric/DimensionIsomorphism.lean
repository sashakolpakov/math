import OAI.AlgebraicGeometry.CycleClass.Geometric.IrreducibleSupportIsomorphism
import OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Dimension Isomorphism -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Dimension-graded cycles under actual isomorphisms

An isomorphism over the complex base carries every irreducible closed support
to its ordinary image. The actual reduced support and its closed image have
the same function-field dimension. Together with invariance of the ambient
function field, this proves preservation of the dimension-based codimension.

The resulting equivalence of support labels induces the coefficient-preserving
linear equivalence of finitely supported algebraic cycles. All maps here are
induced by isomorphisms; no pullback for an arbitrary morphism is asserted.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u v

section SupportDimension

variable {X Y : Scheme.{u}} {K : Type u} [Field K]

/-- The actual closed image of a reduced support is the transported support. -/
theorem DimensionIsomorphism.irreducibleSupportIsoEquiv_eq_imageClosure (e : X ≅ Y)
    (S : IrreducibleCloseds X) :
    StratumClosure.integralImageClosure (GenericPoint.reducedSupportι S ≫ e.hom) =
      IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e S := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (e.hom ∘ GenericPoint.reducedSupportι S)) = _
  rw [Set.range_comp, GenericPoint.range_reducedSupportι]
  exact (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e S).isClosed.closure_eq

/-- Isomorphism transport preserves the dimension of the actual reduced
support over the specified scalar field. -/
theorem DimensionIsomorphism.irreducibleSupportIsoEquiv_transcendenceDimension (e : X ≅ Y)
    (S : IrreducibleCloseds X) (f : Y ⟶ Spec (.of K)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e S) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension S (e.hom ≫ f) := by
  have h := StratumClosure.schemeTranscendenceDimension_eq_imageClosure
    (GenericPoint.reducedSupportι S ≫ e.hom) f
  rw [DimensionIsomorphism.irreducibleSupportIsoEquiv_eq_imageClosure] at h
  simpa only [Foundations.Scheme.SupportDimension.supportTranscendenceDimension, SupportFiniteType.supportStructureMap, Category.assoc] using h.symm

end SupportDimension

variable {V W U : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- An actual isomorphism over the complex base preserves ambient
function-field transcendence dimension. -/
theorem DimensionIsomorphism.varietyIso_transcendenceDimension (e : V.toOver ≅ W.toOver) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension W.structureMap := by
  let i : V.carrier ≅ W.carrier := (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i.hom W.structureMap
  have he : i.hom ≫ W.structureMap = V.structureMap := Over.w e.hom
  rwa [he] at h

/-- The actual reduced support's complex function-field dimension is unchanged. -/
theorem DimensionIsomorphism.varietyIso_supportTranscendenceDimension (e : V.toOver ≅ W.toOver)
    (S : IrreducibleCloseds V.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension
        (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) S) W.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension S V.structureMap := by
  have he : ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e).hom ≫ W.structureMap =
      V.structureMap := Over.w e.hom
  have h := DimensionIsomorphism.irreducibleSupportIsoEquiv_transcendenceDimension
    ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) S W.structureMap
  rwa [he] at h

/-- Codimension as the difference of genuine function-field dimensions is
preserved under an isomorphism over the complex base. -/
theorem DimensionIsomorphism.dimensionCodimension_iso (e : V.toOver ≅ W.toOver)
    (S : IrreducibleCloseds V.carrier) :
    DimensionCycles.dimensionCodimension W
        (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) S) =
      DimensionCycles.dimensionCodimension V S := by
  exact congrArg₂ Nat.sub (DimensionIsomorphism.varietyIso_transcendenceDimension e).symm
    (DimensionIsomorphism.varietyIso_supportTranscendenceDimension e S)

/-- Actual irreducible supports of any fixed dimension-based codimension
are equivalent under an isomorphism over the complex base. -/
def DimensionIsomorphism.dimensionCycleSupportIsoEquiv (e : V.toOver ≅ W.toOver) (p : ℕ) :
    DimensionCycles.DimensionCycleSupport V p ≃ DimensionCycles.DimensionCycleSupport W p :=
  (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e)).subtypeEquiv
    (fun S => Iff.of_eq (congrArg (fun n : ℕ => n = p) (DimensionIsomorphism.dimensionCodimension_iso e S).symm))

@[simp]
theorem DimensionIsomorphism.dimensionCycleSupportIsoEquiv_val (e : V.toOver ≅ W.toOver) (p : ℕ)
    (S : DimensionCycles.DimensionCycleSupport V p) :
    (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p S).val =
      IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) S.val :=
  rfl

/-- The transported support is literally the image under the underlying
scheme isomorphism. -/
@[simp]
theorem DimensionIsomorphism.dimensionCycleSupportIsoEquiv_coe (e : V.toOver ≅ W.toOver) (p : ℕ)
    (S : DimensionCycles.DimensionCycleSupport V p) :
    ((DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p S).val : Set W.carrier) =
      e.hom.left '' (S.val : Set V.carrier) :=
  rfl

@[simp]
theorem DimensionIsomorphism.dimensionCycleSupportIsoEquiv_genericPoint (e : V.toOver ≅ W.toOver) (p : ℕ)
    (S : DimensionCycles.DimensionCycleSupport V p) :
    (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p S).genericPoint = e.hom.left S.genericPoint :=
  IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv_genericPoint ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) S.val

@[simp]
theorem DimensionIsomorphism.dimensionCycleSupportIsoEquiv_symm (e : V.toOver ≅ W.toOver) (p : ℕ) :
    (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p).symm = DimensionIsomorphism.dimensionCycleSupportIsoEquiv e.symm p := by
  apply Equiv.ext
  intro S
  apply Subtype.ext
  rfl

@[simp]
theorem DimensionIsomorphism.dimensionCycleSupportIsoEquiv_refl (p : ℕ) :
    DimensionIsomorphism.dimensionCycleSupportIsoEquiv (Iso.refl V.toOver) p =
      Equiv.refl (DimensionCycles.DimensionCycleSupport V p) := by
  apply Equiv.ext
  intro S
  apply Subtype.ext
  exact congrArg (fun f => f S.val) (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv_refl (X := V.carrier))

@[simp]
theorem DimensionIsomorphism.dimensionCycleSupportIsoEquiv_trans
    (e : V.toOver ≅ W.toOver) (f : W.toOver ≅ U.toOver) (p : ℕ) :
    DimensionIsomorphism.dimensionCycleSupportIsoEquiv (e.trans f) p =
      (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p).trans (DimensionIsomorphism.dimensionCycleSupportIsoEquiv f p) := by
  apply Equiv.ext
  intro S
  apply Subtype.ext
  exact congrArg (fun g => g S.val)
    (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv_trans
      ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso f))

variable {R : Type v} [Semiring R] {p : ℕ}

/-- Relabel dimension-graded cycles by an actual isomorphism over the base. -/
def DimensionCycles.DimensionCycle.isoLinearEquiv (R : Type v) [Semiring R] (e : V.toOver ≅ W.toOver) (p : ℕ) :
    DimensionCycles.DimensionCycle R V p ≃ₗ[R] DimensionCycles.DimensionCycle R W p :=
  Finsupp.domLCongr (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p)

/-- The coefficient at a target support is the coefficient at its inverse image. -/
@[simp]
theorem DimensionCycles.DimensionCycle.isoLinearEquiv_apply (e : V.toOver ≅ W.toOver) (z : DimensionCycles.DimensionCycle R V p)
    (S : DimensionCycles.DimensionCycleSupport W p) :
    DimensionCycles.DimensionCycle.isoLinearEquiv R e p z S = z ((DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p).symm S) :=
  rfl

/-- Transport leaves the coefficient of every transported support unchanged. -/
@[simp]
theorem DimensionCycles.DimensionCycle.isoLinearEquiv_apply_image (e : V.toOver ≅ W.toOver) (z : DimensionCycles.DimensionCycle R V p)
    (S : DimensionCycles.DimensionCycleSupport V p) :
    DimensionCycles.DimensionCycle.isoLinearEquiv R e p z (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p S) = z S := by
  rw [DimensionCycles.DimensionCycle.isoLinearEquiv_apply, Equiv.symm_apply_apply]

/-- In particular, an irreducible cycle generator maps to its actual image
with exactly the original coefficient. -/
@[simp]
theorem DimensionCycles.DimensionCycle.isoLinearEquiv_single (e : V.toOver ≅ W.toOver)
    (S : DimensionCycles.DimensionCycleSupport V p) (r : R) :
    DimensionCycles.DimensionCycle.isoLinearEquiv R e p (Finsupp.single S r) =
      Finsupp.single (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p S) r :=
  Finsupp.domLCongr_single _ _ _

/-- Finite cycle support is carried to the image of the original finite set. -/
theorem DimensionCycles.DimensionCycle.isoLinearEquiv_support (e : V.toOver ≅ W.toOver) (z : DimensionCycles.DimensionCycle R V p) :
    (DimensionCycles.DimensionCycle.isoLinearEquiv R e p z).support =
      z.support.map (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p).toEmbedding :=
  rfl

@[simp]
theorem DimensionCycles.DimensionCycle.isoLinearEquiv_symm (e : V.toOver ≅ W.toOver) (p : ℕ) :
    (DimensionCycles.DimensionCycle.isoLinearEquiv R e p).symm = DimensionCycles.DimensionCycle.isoLinearEquiv R e.symm p := by
  unfold DimensionCycles.DimensionCycle.isoLinearEquiv
  rw [Finsupp.domLCongr_symm, DimensionIsomorphism.dimensionCycleSupportIsoEquiv_symm]

@[simp]
theorem DimensionCycles.DimensionCycle.isoLinearEquiv_refl (p : ℕ) :
    DimensionCycles.DimensionCycle.isoLinearEquiv R (Iso.refl V.toOver) p =
      LinearEquiv.refl R (DimensionCycles.DimensionCycle R V p) := by
  unfold DimensionCycles.DimensionCycle.isoLinearEquiv
  rw [DimensionIsomorphism.dimensionCycleSupportIsoEquiv_refl, Finsupp.domLCongr_refl]

@[simp]
theorem DimensionCycles.DimensionCycle.isoLinearEquiv_trans (e : V.toOver ≅ W.toOver) (f : W.toOver ≅ U.toOver) (p : ℕ) :
    DimensionCycles.DimensionCycle.isoLinearEquiv R (e.trans f) p =
      (DimensionCycles.DimensionCycle.isoLinearEquiv R e p).trans (DimensionCycles.DimensionCycle.isoLinearEquiv R f p) := by
  unfold DimensionCycles.DimensionCycle.isoLinearEquiv
  rw [DimensionIsomorphism.dimensionCycleSupportIsoEquiv_trans, Finsupp.domLCongr_trans]

/-- Pullback along an actual isomorphism is the inverse relabeling. -/
def DimensionCycles.DimensionCycle.isoPullback (R : Type v) [Semiring R] (e : V.toOver ≅ W.toOver) (p : ℕ) :
    DimensionCycles.DimensionCycle R W p ≃ₗ[R] DimensionCycles.DimensionCycle R V p :=
  DimensionCycles.DimensionCycle.isoLinearEquiv R e.symm p

@[simp]
theorem DimensionCycles.DimensionCycle.isoPullback_apply (e : V.toOver ≅ W.toOver) (z : DimensionCycles.DimensionCycle R W p)
    (S : DimensionCycles.DimensionCycleSupport V p) :
    DimensionCycles.DimensionCycle.isoPullback R e p z S = z (DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p S) :=
  rfl

@[simp]
theorem DimensionCycles.DimensionCycle.isoPullback_isoLinearEquiv (e : V.toOver ≅ W.toOver) (z : DimensionCycles.DimensionCycle R V p) :
    DimensionCycles.DimensionCycle.isoPullback R e p (DimensionCycles.DimensionCycle.isoLinearEquiv R e p z) = z := by
  change DimensionCycles.DimensionCycle.isoLinearEquiv R e.symm p (DimensionCycles.DimensionCycle.isoLinearEquiv R e p z) = z
  rw [← DimensionCycles.DimensionCycle.isoLinearEquiv_symm]
  exact (DimensionCycles.DimensionCycle.isoLinearEquiv R e p).symm_apply_apply z

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
