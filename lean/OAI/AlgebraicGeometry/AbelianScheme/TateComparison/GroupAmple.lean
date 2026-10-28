import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CubeProductLift
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricChowModification
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveModification
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Group Ample -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GroupAmple

noncomputable section

section

/-! The theorem of the square for translations of an actual proper
smooth connected commutative group. Projectivity is not an input. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

omit [IsAlgClosed K] in
def groupConstant {T : Over (Spec (.of K))} (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) : T ⟶ A :=
  toUnit T ≫ x

omit [IsAlgClosed K] [GrpObj A] [IsCommMonObj A] in
theorem picardValue_constant (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (.of K))}
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (groupConstant A (T := T) x) = 1 := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.hom ≫ x.left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have hx : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass x.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Spec (.of K)) :=
    Quotient.sound (Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field x.left L)
  rw [hx, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  rfl

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]

theorem cube_identity_two_constants (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (a b : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A L (𝟙 A) (groupConstant A a) (groupConstant A b) = 1 := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  have : IsIntegral A.left := ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral A.hom
  have : GeometricallyIrreducible A.hom :=
    ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_proper_geometricallyConnected_is_geometricallyIrreducible A.hom
  have : GeometricallyReduced A.hom := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth A.hom
  have : GeometricallyIntegral A.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible A.hom
  let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom
  have : IsProper D.projection := D.proper
  have : Surjective D.projection := D.surjective
  have : IsProper (D.projection ≫ A.hom) := inferInstance
  have : GeometricallyIntegral (D.projection ≫ A.hom) := D.geometricallyIntegral A.hom
  let Z := Over.mk (D.projection ≫ A.hom)
  have : IsProper Z.hom := inferInstanceAs (IsProper (D.projection ≫ A.hom))
  have : GeometricallyIntegral Z.hom := D.geometricallyIntegral A.hom
  let p : Z ⟶ A := Over.homMk D.projection rfl
  have hp : Surjective p.left := D.surjective
  have : LocallyOfFiniteType p.left := inferInstanceAs (LocallyOfFiniteType D.projection)
  obtain ⟨z₀, hz₀⟩ := IsogenyQuotient.Geometric.Points.Construction.surjective_on_geometric_points p K (𝟙 (Spec (.of K))) (MonObj.one (X := A))
  obtain ⟨za, hza⟩ := IsogenyQuotient.Geometric.Points.Construction.surjective_on_geometric_points p K (𝟙 (Spec (.of K))) a
  have hzero : z₀.left ≫ D.projection = Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin A := congrArg Over.Hom.left hz₀
  have hmod := CubeProductLift.modifiedCube_trivial A Z.hom Z.hom D.sectionCover D.sectionCover
    D.projection rfl D.projection rfl z₀.left z₀.w hzero z₀.left z₀.w hzero L
  have hz := CubeProductLift.cube_eq_one_of_modifiedCube_trivial A Z.hom Z.hom
    D.projection rfl D.projection rfl L hmod (𝟙 Z) (toUnit Z ≫ za) (groupConstant A (T := Z) b)
  have hn (x : A.left) : IsIntegrallyClosed (A.left.presheaf.stalk x) := by
    have := Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk A.hom x
    infer_instance
  apply D.picard_injective hn
  rw [map_one]
  change Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map p.left
    (Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A L (𝟙 A) (groupConstant A a) (groupConstant A b)) = 1
  rw [Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.pullback A L p]
  change za ≫ p = a at hza
  change Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A L (𝟙 Z ≫ p) ((toUnit Z ≫ za) ≫ p) (toUnit Z ≫ b) = 1 at hz
  rw [Category.id_comp, Category.assoc, hza] at hz
  simpa only [Category.comp_id, groupConstant, ← Category.assoc, comp_toUnit] using hz

theorem translation_picard_square (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (GrpObj.mulRight a).hom.left) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (GrpObj.mulRight a⁻¹).hom.left) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ 2 := by
  have hc := div_eq_one.mp (cube_identity_two_constants A L a a⁻¹)
  have hi : groupConstant A (T := A) a⁻¹ = (groupConstant A a)⁻¹ :=
    GrpObj.comp_inv (toUnit A) a
  have hid : Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  change Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A * groupConstant A a * groupConstant A a⁻¹) *
      Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A) * Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (groupConstant A a) *
      Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (groupConstant A a⁻¹) =
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A * groupConstant A a) *
      Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A * groupConstant A a⁻¹) *
      Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (groupConstant A a * groupConstant A a⁻¹) at hc
  have hp : groupConstant A (T := A) a * groupConstant A a⁻¹ = 1 := by
    rw [hi, mul_inv_cancel]
  have ht : (𝟙 A : A ⟶ A) * groupConstant A a * groupConstant A a⁻¹ = 𝟙 A := by
    rw [mul_assoc, hp, mul_one]
  rw [picardValue_constant, picardValue_constant, ht, hp,
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value_one, hid, mul_one, mul_one, mul_one] at hc
  exact hc.symm.trans (pow_two _).symm

end

/-! Constructing an ample line bundle on the actual proper smooth
connected group from affine section neighborhoods and translation squares. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]

omit [Smooth A.hom] in
theorem exists_opposite_translates_mem (U : A.left.Opens) (hne : (U : Set A.left).Nonempty)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    ∃ a : 𝟙_ (Over (Spec (.of K))) ⟶ A,
      (GrpObj.mulRight a).hom.left (x.left (IsLocalRing.closedPoint K)) ∈ U ∧
      (GrpObj.mulRight a⁻¹).hom.left (x.left (IsLocalRing.closedPoint K)) ∈ U := by
  have : IrreducibleSpace A.left := Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let α := Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A x
  let β : A.left ≅ A.left := (Over.forget (Spec (.of K))).mapIso (asIso (GrpObj.inv (X := A))) ≪≫ α
  let V := α.hom ⁻¹ᵁ U
  let W := β.hom ⁻¹ᵁ U
  have hV : (Set.univ ∩ (V : Set A.left)).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨α.inv y, trivial, by
      change α.hom (α.inv y) ∈ U
      rw [Scheme.inv_hom_apply]
      exact hy⟩
  have hW : (Set.univ ∩ (W : Set A.left)).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨β.inv y, trivial, by
      change β.hom (β.inv y) ∈ U
      rw [Scheme.inv_hom_apply]
      exact hy⟩
  have hinter : ((V ⊓ W : A.left.Opens) : Set A.left).Nonempty := by
    have h := (IrreducibleSpace.isIrreducible_univ A.left).2 V W V.isOpen W.isOpen hV hW
    obtain ⟨z, _, hzV, hzW⟩ := h
    exact ⟨z, hzV, hzW⟩
  obtain ⟨a₀, ha₀, hac⟩ := nonempty_inter_closedPoints hinter (V ⊓ W).isOpen.isLocallyClosed
  let a : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom a₀ hac) (pointOfClosedPoint_comp A.hom a₀ hac)
  have ha : a.left (IsLocalRing.closedPoint K) = a₀ := pointOfClosedPoint_apply A.hom a₀ hac _
  have he₁ := congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
    (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.exchange A x a)
  have he₂ := congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
    (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.exchange A x a⁻¹)
  refine ⟨a, ?_, ?_⟩
  · change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom (x.left (IsLocalRing.closedPoint K)) ∈ U
    have he : (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom (x.left (IsLocalRing.closedPoint K)) =
        α.hom a₀ := he₁.trans (congrArg α.hom ha)
    exact he.symm ▸ ha₀.1
  · change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom (x.left (IsLocalRing.closedPoint K)) ∈ U
    have he : (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom (x.left (IsLocalRing.closedPoint K)) =
        β.hom a₀ := he₂.trans (congrArg β.hom ha)
    exact he.symm ▸ ha₀.2

theorem groupLineBundle_ample_of_affine_section (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf)
    (hne : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set A.left).Nonempty)
    (haff : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)) : L.IsAmple := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : A.left.IsSeparated := ⟨by rw [← terminal.comp_from A.hom]; infer_instance⟩
  apply L.isAmple_iff_tensorPower.mpr
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x).closure
    isClosed_closure.isLocallyClosed
  let yp : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hyc) (pointOfClosedPoint_comp A.hom y hyc)
  have hyp : yp.left (IsLocalRing.closedPoint K) = y := pointOfClosedPoint_apply A.hom y hyc _
  obtain ⟨a, hya, hyb⟩ := exists_opposite_translates_mem A (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) hne yp
  rw [hyp] at hya hyb
  let f := (GrpObj.mulRight a).hom.left
  let g := (GrpObj.mulRight a⁻¹).hom.left
  have : IsIso f := (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).isIso_hom
  have : IsIso g := (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).isIso_hom
  let M := (L.pullback f).tensor (L.pullback g)
  let t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ M.sheaf :=
    Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s)
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ g ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing (L := L.pullback f) (M := L.pullback g)
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s)).trans
      (congrArg₂ (· ⊓ ·) (Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f L s)
        (Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback g L s))
  have hclass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower 2) :=
    (translation_picard_square A L a).trans (Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow L 2).symm
  obtain ⟨e⟩ := Quotient.exact hclass
  refine ⟨2, by decide, t ≫ e.hom, ?_, ?_⟩
  · rw [AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, ht]
    apply (specializes_iff_mem_closure.mpr hy).mem_open
      (f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ g ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).isOpen
    exact ⟨hya, hyb⟩
  · rw [AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, ht]
    exact (haff.preimage f).inf (haff.preimage g)

theorem properGroup_exists_ample : ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left, L.IsAmple := by
  let x := (MonObj.one (X := A)).left (IsLocalRing.closedPoint K)
  obtain ⟨L, s, hx, hs, _⟩ := Quotients.FiniteDescent.SymmetricAffine.Construction.SymmetricAffineSections.exists_for_group A x
  exact ⟨L, groupLineBundle_ample_of_affine_section A L s ⟨x, hx⟩ hs⟩

def properGroupProjectivePresentation : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A :=
  (properGroup_exists_ample A).choose_spec.projectivePresentation A.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GroupAmple
