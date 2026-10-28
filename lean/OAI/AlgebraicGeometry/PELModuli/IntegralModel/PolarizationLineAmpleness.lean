import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor

/-! # Polarization Line Ampleness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineAmpleness.PolarizationAmpleness

noncomputable section

/-! A positive polarization gives an ample canonical Poincare diagonal
bundle. Its class is the tensor product of an ample inducing bundle and
its pullback by inversion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass.PoincareClasses

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme)

def biextensionClass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.scheme ⊗ A.scheme).left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ell ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

omit [IsAlgClosed k] in
theorem biextensionClass_evaluate {T : Over (Spec (.of k))} (a b : T ⟶ A.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a b).left (biextensionClass D ell) =
      PoincareClass.PoincareClasses.pairClass D (a ≫ ell) b := by
  have h : (lift a b).left ≫ (ell ⊗ₘ 𝟙 A.scheme).left = (lift (a ≫ ell) b).left := by
    simpa only [Category.comp_id, Over.comp_left] using
      congrArg Over.Hom.left (lift_map a b ell (𝟙 A.scheme))
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (lift a b).left (ell ⊗ₘ 𝟙 A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm.trans
    (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) h)

local instance abelian_compact : CompactSpace A.scheme.left :=
  QuasiCompact.compactSpace_of_compactSpace A.scheme.hom

local instance abelian_quasiSeparated : QuasiSeparatedSpace A.scheme.left :=
  quasiSeparatedSpace_of_quasiSeparated A.scheme.hom

theorem polarizationLine_symmetrization (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (1 : A.scheme ⟶ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (hFormula : biextensionClass D ell *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A.scheme].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareClass.PoincareClasses.polarizationLine D ell) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor (L.pullback (GrpObj.inv (X := A.scheme)).left)) := by
  let z := lift (𝟙 A.scheme) (GrpObj.inv (X := A.scheme))
  have hf : z.left ≫ (fst A.scheme A.scheme).left = 𝟙 A.scheme.left :=
    congrArg Over.Hom.left (lift_fst (𝟙 A.scheme) (GrpObj.inv (X := A.scheme)))
  have hs : z.left ≫ (snd A.scheme A.scheme).left = (GrpObj.inv (X := A.scheme)).left :=
    congrArg Over.Hom.left (lift_snd (𝟙 A.scheme) (GrpObj.inv (X := A.scheme)))
  have hm : z.left ≫ μ[A.scheme].left = (1 : A.scheme ⟶ A.scheme).left := by
    have he : z ≫ μ[A.scheme] = 1 := by
      change (𝟙 A.scheme) * (GrpObj.inv (X := A.scheme)) = 1
      rw [GrpObj.inv_eq_inv, mul_inv_cancel]
    exact congrArg Over.Hom.left he
  have h := congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left) hFormula
  rw [map_mul, map_mul] at h
  have hp : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left (biextensionClass D ell) =
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareClass.PoincareClasses.polarizationLine D ell))⁻¹ := by
    have h₀ := biextensionClass_evaluate D ell (𝟙 A.scheme) (GrpObj.inv (X := A.scheme))
    rw [Category.id_comp, GrpObj.inv_eq_inv, PoincareClass.PoincareClasses.pairClass_inv_right] at h₀
    exact h₀
  have pbf : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left
      (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
    exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp z.left (fst A.scheme A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      ((congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hf).trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))
  have pbs : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left
      (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (GrpObj.inv (X := A.scheme)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
    exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp z.left (snd A.scheme A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hs)
  have pbm : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left
      (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A.scheme].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = 1 := by
    exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp z.left μ[A.scheme].left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      ((congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hm).trans hzero)
  rw [hp, pbf, pbs, pbm, mul_assoc] at h
  exact inv_mul_eq_one.mp h

theorem polarizationLine_isAmple_of_presentation (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (1 : A.scheme ⟶ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (hFormula : biextensionClass D ell *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A.scheme].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    (PoincareClass.PoincareClasses.polarizationLine D ell).IsAmple := by
  have : A.scheme.left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from A.scheme.hom]
    infer_instance⟩
  have : IsIso (GrpObj.inv (X := A.scheme)).left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map (GrpObj.inv (X := A.scheme))))
  obtain ⟨e⟩ := Quotient.exact (polarizationLine_symmetrization D ell L hzero hFormula)
  exact (AmpleTensor.PolarizationAmpleness.tensor_isAmple hL (hL.pullback_of_isIso (GrpObj.inv (X := A.scheme)).left)).of_iso e.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineAmpleness.PolarizationAmpleness
