import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemePointPicardPairing

/-! # Cubical Inducing Point Classes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingPointClasses

noncomputable section

/-! The proved geometric cube pairing is the actual difference class of the inducing line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemePointPicardPairing.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass.Bundle

theorem difference_formula {G : Type*} [CommGroup G] (x y z : G) : x / y / z * y * z = x := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (.of k))} (a b : T ⟶ A)

/-- The geometric cube pairing satisfies the original inducing formula at every pair of test points. -/
theorem pairing_formula :
    (FormalGeometry.Completion.SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul a) (Additive.ofMul b)).toMul *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass b.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a * b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  let : CommGroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) := Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard.instCommGroupIsoClass
  change Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (a * b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
    Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
    Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map b.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
    Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
    Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map b.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (a * b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  exact difference_formula _ _ _

attribute [local instance] Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup

/-- No dual-sheaf choice changes the intrinsic class: multiplication determines the difference uniquely. -/
theorem pairing_eq :
    (FormalGeometry.Completion.SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul a) (Additive.ofMul b)).toMul =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a b).left (InducingClass.Bundle.lineClass A L) := by
  let : CommGroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) := Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup T.left
  rw [InducingClass.Bundle.lineClass_atPoint, div_div]
  apply eq_div_iff_mul_eq'.mpr
  exact (mul_assoc _ _ _).symm.trans (pairing_formula A L a b)

/-- The full actual product-line class is recovered at the universal pair. -/
theorem universal_class :
    (FormalGeometry.Completion.SchemePointPicardPairing.Construction.polarizationLineClass A L).toMul = InducingClass.Bundle.lineClass A L := by
  have h := pairing_eq A L (fst A A) (snd A A)
  have he : lift (fst A A) (snd A A) = 𝟙 (A ⊗ A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change (FormalGeometry.Completion.SchemePointPicardPairing.Construction.polarizationLineClass A L).toMul =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (fst A A) (snd A A)).left (InducingClass.Bundle.lineClass A L) at h
  rw [he] at h
  exact h.trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingPointClasses
