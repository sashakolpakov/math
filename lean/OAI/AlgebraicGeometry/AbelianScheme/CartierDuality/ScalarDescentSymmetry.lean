import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.OrdinaryGlobalLineDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineRecoveryUniqueness

/-! # Scalar Descent Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarDescentSymmetry.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: symmetries of scalar gluing descend to actual line isomorphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of ordinary data has the native compatibility equation. -/
theorem nativeDatumHom_compatible
    (D E : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) (b : D ⟶ E)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D) (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f E)
      (b.hom PUnit.unit) q x y hx hy := b.comm q x y hx hy

/-- Equal framed scalars identify the full ordinary descent objects. -/
def nativeDatumIso_of_framedScalars
    (D E : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d : E.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (hs : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q),
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D) e q x y hx hy =
        Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f E) d q x y hx hy) : D ≅ E :=
  IntrinsicDescentRecovery.Construction.LineDescent.nativeDatumIso f D E (e ≪≫ d.symm) (fun q x y hx hy =>
    Picard.Homomorphisms.FramedDescentComparison.Construction.framedDescentScalar_eq_implies_compatible (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D)
      (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f E) e d q x y hx hy (hs q x y hx hy))

variable (s : Y ⟶ Y) (t : X ⟶ X) (w : t ≫ f = f ≫ s) (C : ScalarLineGluing.Construction.LineDescent.ScalarCocycle f)

/-- The exact scalar condition for a square of covers to preserve the given gluing. -/
def PreservesScalarCocycle : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q),
    C.value (q ≫ s) (x ≫ t) (y ≫ t)
      (by rw [Category.assoc, w, ← Category.assoc, hx])
      (by rw [Category.assoc, w, ← Category.assoc, hy]) = C.value q x y hx hy

variable (hc : PreservesScalarCocycle f s t w C)

/-- A scalar-preserving square acts on the complete original descent datum. -/
def scalarDatumSquareIso :
    (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f s t w).obj (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData C.nativeDatum) ≅
      AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData C.nativeDatum := by
  apply nativeDatumIso_of_framedScalars f _ _
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) t) (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))
  intro T q x y hx hy
  have hs := FramedBaseChange.Construction.LineDescent.framedDescentScalar_square f f s t w (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData C.nativeDatum)
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) q x y hx hy
  exact hs.trans ((C.nativeDatum_scalar (q ≫ s) (x ≫ t) (y ≫ t)
    (by rw [Category.assoc, w, ← Category.assoc, hx])
    (by rw [Category.assoc, w, ← Category.assoc, hy])).trans
      ((hc q x y hx hy).trans (C.nativeDatum_scalar q x y hx hy).symm))

variable [IsAffineHom f] [Flat f] [Surjective f]

/-- An isomorphism of complete canonical data descends to an actual line isomorphism. -/
theorem lineIso_of_ordinaryIso (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (b : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L.sheaf ≅
      (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M.sheaf) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let e := (Picard.Homomorphisms.ModuleHomBaseChange.Construction.nativeDescentEvaluation f).mapIso b
  obtain ⟨a, _, _⟩ := LineRecoveryUniqueness.Construction.LineDescent.existsUnique_lineIso_descent f L M e
    (nativeDatumHom_compatible f _ _ b.hom)
  exact ⟨a⟩

/-- A symmetry of arbitrary recovered data gives a symmetry of its descended line. -/
theorem linePullbackIso_of_datumSymmetry (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (r : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L.sheaf ≅ D)
    (a : (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f s t w).obj D ≅ D) :
    Nonempty ((Scheme.Modules.pullback s).obj L.sheaf ≅ L.sheaf) :=
  lineIso_of_ordinaryIso f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback s L) L
    (((Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareComparison f f s t w).app L.sheaf).symm ≪≫
      (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f s t w).mapIso r ≪≫ a ≪≫ r.symm)

include hc in
/-- Symmetry of the actual scalar gluing gives an isomorphism of the constructed global line. -/
theorem scalarDescendedLine_symmetry :
    let L := OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLine f C.nativeDatum (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X).locallyTrivial
    Nonempty ((Scheme.Modules.pullback s).obj L.sheaf ≅ L.sheaf) :=
  linePullbackIso_of_datumSymmetry f s t w
    (OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLine f C.nativeDatum (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X).locallyTrivial)
    (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData C.nativeDatum)
    (OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso f C.nativeDatum (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X).locallyTrivial)
    (scalarDatumSquareIso f s t w C hc)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarDescentSymmetry.Construction.LineDescent
