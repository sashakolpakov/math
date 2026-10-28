import OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleHomogeneousPair
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleDifferenceSurjectivity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceParameterTransport
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClosedSheafification

/-! # Geometric Ample Difference Surjectivity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GeometricAmpleDifferenceSurjectivity.Geometric

noncomputable section

section

/-! Every actual ample line on a projective abelian scheme over an
arbitrary algebraically closed characteristic-zero field realizes every
homogeneous line by translation in the original relative Picard sheaf.
A countable field model and its complex embedding are constructed. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClosedSheafification

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem geometric_ampleDifference_realizes_homogeneous_line (hL : L.IsAmple)
    (hN : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N)) : DifferenceParameterTransport.Geometric.HasDifferenceParameter A L N := by
  obtain ⟨D, J, hJ, hJrecover⟩ := CountableAmpleHomogeneousPair.Geometric.exists_countable_ample_homogeneous_pair A L N hL hN
  have hrep : DifferenceParameterTransport.Geometric.HasDifferenceParameter D.abelian D.line J :=
    CountableAmpleDifferenceSurjectivity.Geometric.countable_ampleDifference_realizes_homogeneous_line D.abelian D.line J D.ample hJ
  let u := Spec.map (CommRingCat.ofHom D.field.subtype)
  let B := D.abelian.pullback u
  let p : B.scheme.left ⟶ D.abelian.scheme.left := pullback.fst D.abelian.scheme.hom u
  have hLrec : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass D.recovery.hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line.pullback p)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp D.recovery.hom.left p (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.line)).symm.trans
      D.line_recovery
  have hNrec : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass D.recovery.hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (J.pullback p)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N :=
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp D.recovery.hom.left p (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J)).symm.trans hJrecover
  exact DifferenceParameterTransport.Geometric.HasDifferenceParameter.of_groupIso A B D.recovery L N (D.line.pullback p) (J.pullback p)
    hLrec hNrec (DifferenceParameterTransport.Geometric.HasDifferenceParameter.baseChange D.abelian D.line J u hrep)

end

/-! Translation by an actual ample line realizes every section of
the original homogeneous Picard sheaf at an arbitrary geometric
characteristic-zero field point. The underlying line is constructed. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem geometric_ampleDifference_surjective (hL : L.IsAmple)
    (q : A.homogeneousPicardSheaf.obj.obj (.op (Over.mk (𝟙 (Spec (.of k)))))) :
    ∃ a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme,
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
        A.homogeneousPicardSheafInclusion.hom.app (.op (Over.mk (𝟙 (Spec (.of k))))) q := by
  let U := Over.mk (𝟙 (Spec (.of k)))
  obtain ⟨r, hr⟩ := (AbelianModuli.ReferenceFamily.ClosedSheafification.fppf_toSheafify_bijective_at_algClosed (𝟙 (Spec (.of k)))
    A.homogeneousPicardPresheaf).surjective q
  let t : A.scheme ⟶ U := Over.mkIdTerminal.from A.scheme
  let j : A.scheme ⟶ U ⊗ A.scheme := lift t (𝟙 A.scheme)
  have hj : snd U A.scheme ≫ j = 𝟙 (U ⊗ A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [j, Category.assoc, lift_fst, Category.id_comp]
      exact Over.mkIdTerminal.hom_ext _ _
    · simp [j]
  let q₀ : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left := r.val
  have hq₀ : A.IsHomogeneousPicardClass U q₀ := r.property
  have hout : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q₀.out = q₀ := Quotient.out_eq q₀
  let N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left := q₀.out.pullback j.left
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) = q₀ := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q₀.out)) = _
    rw [hout, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q₀)
      (congrArg Over.Hom.left hj)).trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q₀)
  have hN : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) := by
    change A.IsHomogeneousPicardClass U
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N))
    exact (congrArg (A.IsHomogeneousPicardClass U) hc).mpr hq₀
  obtain ⟨a, ha⟩ := geometric_ampleDifference_realizes_homogeneous_line A L N hL hN
  have hq : A.homogeneousPicardSheafInclusion.hom.app (.op U) q =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) q₀ :=
    (congrArg (A.homogeneousPicardSheafInclusion.hom.app (.op U)) hr).symm.trans
      (HomogeneousBaseChangeForgetting.Geometric.homogeneousForget_toSheafify A U r)
  exact ⟨a, ha.trans ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) hc).trans hq.symm)⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GeometricAmpleDifferenceSurjectivity.Geometric
