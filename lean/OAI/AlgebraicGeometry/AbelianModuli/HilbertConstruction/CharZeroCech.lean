import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.SchemeStructureBound
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.RepresentationTheory.Theta.Geometric.ConstantFiberDimension
import OAI.RepresentationTheory.Theta.Geometric.ZariskiBaseDimension
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleLine
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableComplexEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationAmpleBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint

/-! # Char Zero Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharZeroCech

noncomputable section

/-! The structure-sheaf H1 bound for arbitrary projective abelian schemes
in characteristic zero. Countable field models and the genuine field
base-change map reduce the calculation to the original complex bound. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

theorem complexAbelian_structureCechH1_finrank_le
    {g : ℕ} (A : Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    {I : Type} [LinearOrder I] [Finite I] (U : I → A.scheme.left.Opens)
    (hU : IsOpenCover U) (haU : ∀ i, IsAffineOpen (U i)) :
    Module.finrank Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (Line.Bundles.structureModule A.scheme.left) U).sc' 0 1 2).homology ≤ g := by
  let PN := ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation P
  let B := ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PN
  let : A.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.scheme.hom]
    infer_instance
  let : (Line.Bundles.structureModule A.scheme.left).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (Line.Bundles.LineBundle.trivial A.scheme.left)
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule A.scheme.hom (Line.Bundles.structureModule A.scheme.left) 1
  let := ReferenceFamily.StructureComplexScalars.structureH1ComplexModule A.scheme
  have he := ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (Line.Bundles.structureModule A.scheme.left) U).homologyIsoSc'
    0 1 2 (by simp) (by simp)).toLinearEquiv.finrank_eq
  have hdim : Module.finrank Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (Line.Bundles.structureModule A.scheme.left) U).sc' 0 1 2).homology =
      Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (Line.Bundles.structureModule A.scheme.left) 1) :=
    he.symm.trans
      ((SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv A.scheme.hom
        (Line.Bundles.structureModule A.scheme.left) U hU haU 1).finrank_eq.trans
          (RepresentationTheory.Theta.Geometric.ZariskiBaseDimension.zariskiBase_finrank_complex B (Line.Bundles.structureModule A.scheme.left) 1))
  exact hdim.le.trans (ReferenceFamily.Abelian.SchemeStructureBound.abelianSchemeStructureH1_finrank_le A PN)

theorem abelian_structureCechH1_finrank_fieldBaseChange
    {k l : Type} [Field k] [Field l] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : Abelian.Schemes.AbelianScheme g (Spec (.of l)))
    (b : Spec (.of l) ⟶ Spec (.of k)) (f : B.scheme.left ⟶ A.scheme.left)
    (hp : IsPullback f B.scheme.hom A.scheme.hom b)
    {I J : Type} [LinearOrder I] [Finite I] [LinearOrder J]
    (U : I → A.scheme.left.Opens) (V : J → B.scheme.left.Opens)
    (hU : IsOpenCover U) (hV : IsOpenCover V)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ j, IsAffineOpen (V j)) :
    Module.finrank Γ(Spec (.of l), ⊤)
        ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex B.scheme.hom (Line.Bundles.structureModule B.scheme.left) V).sc' 0 1 2).homology =
      Module.finrank Γ(Spec (.of k), ⊤)
        ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (Line.Bundles.structureModule A.scheme.left) U).sc' 0 1 2).homology := by
  let : A.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.scheme.hom]
    infer_instance
  let : B.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from B.scheme.hom]
    infer_instance
  let : (Line.Bundles.structureModule A.scheme.left).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (Line.Bundles.LineBundle.trivial A.scheme.left)
  let : ((Scheme.Modules.pullback f).obj (Line.Bundles.structureModule A.scheme.left)).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent ((Line.Bundles.LineBundle.trivial A.scheme.left).pullback f)
  let : Field Γ(Spec (.of l), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField l
  have hk : IsField Γ(Spec (.of k), ⊤) := by
    let : Field Γ(Spec (.of k), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField k
    exact Field.toIsField _
  exact RepresentationTheory.Theta.Geometric.ConstantFiberDimension.geometricCech_H1_finrank_cover_baseChange hk f A.scheme.hom B.scheme.hom b hp
    (Line.Bundles.structureModule A.scheme.left) (Line.Bundles.structureModule B.scheme.left) (Line.Bundles.structureModulePullbackIso f).symm
      U V hU hV haU haV

theorem algClosedCharZeroAbelian_structureCechH1_finrank_le
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    {I : Type} [LinearOrder I] [Finite I] (U : I → A.scheme.left.Opens)
    (hU : IsOpenCover U) (haU : ∀ i, IsAffineOpen (U i)) :
    Module.finrank Γ(Spec (.of k), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (Line.Bundles.structureModule A.scheme.left) U).sc' 0 1 2).homology ≤ g := by
  obtain ⟨D⟩ := Picard.ThetaConstruction.CountableAmpleLine.Geometric.exists_countable_ample_line_model A P.ampleLineBundle
    P.ampleLineBundle_isAmple
  let PD := D.ample.projectivePresentation D.abelian.scheme.hom
  let UD := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover D.abelian.scheme PD
  have hUD : IsOpenCover UD := IsOpenCover.mk (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers D.abelian.scheme PD)
  have haUD := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.affine D.abelian.scheme PD
  let u := Spec.map (CommRingCat.ofHom D.field.subtype)
  let q := ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme D.abelian.scheme D.recovery
  have hk := abelian_structureCechH1_finrank_fieldBaseChange D.abelian A u q
    (ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap_isPullback u A.scheme D.abelian.scheme D.recovery).flip
      UD U hUD hU haUD haU
  obtain ⟨embedding⟩ := AbelianScheme.TateComparison.CountableComplexEmbedding.countable_field_has_complex_embedding D.field
  let b := Spec.map (CommRingCat.ofHom embedding)
  let C := D.abelian.pullback b
  let PC := PD.baseChange b
  let UC := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover C.scheme PC
  have hUC : IsOpenCover UC := IsOpenCover.mk (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers C.scheme PC)
  have haUC := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.affine C.scheme PC
  have hc := abelian_structureCechH1_finrank_fieldBaseChange D.abelian C b
    (pullback.fst D.abelian.scheme.hom b) (IsPullback.of_hasPullback D.abelian.scheme.hom b)
      UD UC hUD hUC haUD haUC
  exact hk.le.trans (hc.symm.le.trans
    (complexAbelian_structureCechH1_finrank_le C PC UC hUC haUC))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharZeroCech
