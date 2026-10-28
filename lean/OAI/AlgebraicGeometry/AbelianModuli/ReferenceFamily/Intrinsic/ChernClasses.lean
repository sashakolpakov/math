import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity
import OAI.AlgebraicGeometry.DivisorClass.Chern.Iso

/-! # Chern Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses

noncomputable section

/-! The HilbertConstruction line bundles defining a polarization have genuine rational
first Chern classes on the native complex scheme. The adapter preserves
the module sheaf and is invariant under its actual isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def nativeLineBundle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier) :
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X where
  sheaf := L.sheaf
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
    exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e⟩⟩

def lineBundleChernClass (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier) :
    X.rationalCohomology 2 := DivisorClass.Chern.First.firstChernClassQ X (nativeLineBundle X L)

theorem lineBundleChernClass_iso (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L M : HilbertConstruction.Line.Bundles.LineBundle X.carrier) (e : L.sheaf ≅ M.sheaf) :
    lineBundleChernClass X L = lineBundleChernClass X M :=
  (DivisorClass.Chern.Iso.firstChernClassQ_iso X (nativeLineBundle X L) (nativeLineBundle X M) e).symm

def lineBundleClassChernClass (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.carrier → X.rationalCohomology 2 :=
  Quotient.lift (lineBundleChernClass X) (fun L M ⟨e⟩ => lineBundleChernClass_iso X L M e)

theorem lineBundleClassChernClass_classOf (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier) :
    lineBundleClassChernClass X (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = lineBundleChernClass X L := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses
