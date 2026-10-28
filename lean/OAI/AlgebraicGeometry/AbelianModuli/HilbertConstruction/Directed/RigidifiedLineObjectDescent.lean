import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedHeterogeneousPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.FamilyIntrinsicDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CoverLineObjectDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LineNormalization

/-! # Rigidified Line Object Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedLineObjectDescent.DirectedRigidifiedFamilyLines

noncomputable section

/-! Effective descent of actual normalized line objects on a fixed
abelian family, from a directed parameter cover. The only compatibility
input is the original transition class equation. Canonical normalized
comparisons supply the native descent datum on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

private theorem rigidified_hom_congr {X Z : Scheme.{0}} {z : Z ⟶ X}
    {L M : RigidifiedLineBundles.RigidifiedLineBundle z} {e f : RigidifiedLineBundles.RigidifiedLineBundleIso L M} (h : e = f) :
    e.underlying.hom = f.underlying.hom := congrArg (fun q => q.underlying.hom) h

private theorem rigidified_hom_identity {X Z : Scheme.{0}} {z : Z ⟶ X}
    {L : RigidifiedLineBundles.RigidifiedLineBundle z} (e : RigidifiedLineBundles.RigidifiedLineBundleIso L L)
    (h : e = RigidifiedLineBundles.RigidifiedLineBundleIso.refl L) : e.underlying.hom = 𝟙 L.lineBundle.sheaf :=
  rigidified_hom_congr h

private theorem rigidified_hom_composition {X Z : Scheme.{0}} {z : Z ⟶ X}
    {L M N : RigidifiedLineBundles.RigidifiedLineBundle z}
    (e : RigidifiedLineBundles.RigidifiedLineBundleIso L M) (f : RigidifiedLineBundles.RigidifiedLineBundleIso M N)
    (g : RigidifiedLineBundles.RigidifiedLineBundleIso L N) (h : e.trans f = g) :
    e.underlying.hom ≫ f.underlying.hom = g.underlying.hom := rigidified_hom_congr h

private theorem overModulePullHom_reindex
    {S : Scheme.{0}} {X₁ X₂ Y Y' : Over S}
    {L₁ : X₁.left.Modules} {L₂ : X₂.left.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (q : (Scheme.Modules.pullback f₁.left).obj L₁ ⟶
      (Scheme.Modules.pullback f₂.left).obj L₂)
    (t : Y' ⟶ Y) (f₁' : Y' ⟶ X₁) (f₂' : Y' ⟶ X₂)
    (h₁ : t ≫ f₁ = f₁') (h₂ : t ≫ f₂ = f₂') :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
      (X₁ := X₁) (X₂ := X₂) (Y := Y) (Y' := Y')
      (M₁ := L₁) (M₂ := L₂) (f₁ := f₁) (f₂ := f₂) q t f₁' f₂' h₁ h₂ =
      pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks)
        (X₁ := X₁.left) (X₂ := X₂.left) (Y := Y.left) (Y' := Y'.left)
        (M₁ := L₁) (M₂ := L₂) (f₁ := f₁.left) (f₂ := f₂.left)
        q t.left f₁'.left f₂'.left
        (congrArg Over.Hom.left h₁) (congrArg Over.Hom.left h₂) :=
  Picard.PoincareBundle.DescentReindexing.pullHom_reindex (Over.forget S) Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    (X₁ := X₁) (X₂ := X₂) (Y := Y) (Y' := Y')
    (L₁ := L₁) (L₂ := L₂) (f₁ := f₁) (f₂ := f₂) q t f₁' f₂' h₁ h₂

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
  {A : Abelian.Schemes.AbelianScheme g S} {E : Over S} {C : E.left.OpenCover.{0}}
  [Category C.I₀] [C.LocallyDirected] (D : RigidifiedFamilyLines.DirectedRigidifiedFamilyLines A E C)

/-- The canonical comparison commutes with the native pseudofunctor
pullback, with the original endpoint line sheaves unchanged. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.comparison_nativePullback {T U : Over S} (i k : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C k)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C k)
    (t : U ⟶ T) (a' : U ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b' : U ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C k)
    (ha : t ≫ a = a') (hb : t ≫ b = b')
    (h' : a' ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b' ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C k) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (D.comparison i k a b h).underlying.hom
      (t ▷ A.scheme).left (a' ▷ A.scheme).left (b' ▷ A.scheme).left
      (congrArg Over.Hom.left ((comp_whiskerRight t a A.scheme).symm.trans
        (congrArg (fun f => f ▷ A.scheme) ha)))
      (congrArg Over.Hom.left ((comp_whiskerRight t b A.scheme).symm.trans
        (congrArg (fun f => f ▷ A.scheme) hb))) =
      (D.comparison i k a' b' h').underlying.hom := by
  let : Subsingleton (RigidifiedLineBundles.RigidifiedLineBundleIso ((D.line i).familyPullback A a')
      ((D.line k).familyPullback A b')) :=
    RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left
      (A.familyZero_globalFunctions_bijective U).1 _ _
  have he : RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo A a b
      (D.comparison i k a b h) t a' b' ha hb = D.comparison i k a' b' h' :=
    Subsingleton.elim _ _
  exact (RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo_hom A a b
    (D.comparison i k a b h) t a' b' ha hb).symm.trans (rigidified_hom_congr he)

private theorem comparison_overPullback {T U : Over S} (i k : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C k)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C k)
    (t : U ⟶ T) (a' : U ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b' : U ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C k)
    (ha : t ≫ a = a') (hb : t ≫ b = b')
    (h' : a' ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b' ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C k) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
      (X₁ := Embedded.FamilyOpenCover.overOpenCoverObject E C i ⊗ A.scheme)
      (X₂ := Embedded.FamilyOpenCover.overOpenCoverObject E C k ⊗ A.scheme)
      (Y := T ⊗ A.scheme) (Y' := U ⊗ A.scheme)
      (M₁ := (D.line i).lineBundle.sheaf) (M₂ := (D.line k).lineBundle.sheaf)
      (f₁ := a ▷ A.scheme) (f₂ := b ▷ A.scheme)
      (D.comparison i k a b h).underlying.hom
      (t ▷ A.scheme) (a' ▷ A.scheme) (b' ▷ A.scheme)
      ((comp_whiskerRight t a A.scheme).symm.trans (congrArg (fun f => f ▷ A.scheme) ha))
      ((comp_whiskerRight t b A.scheme).symm.trans (congrArg (fun f => f ▷ A.scheme) hb)) =
      (D.comparison i k a' b' h').underlying.hom := by
  have hp := overModulePullHom_reindex
    (S := S) (X₁ := Embedded.FamilyOpenCover.overOpenCoverObject E C i ⊗ A.scheme)
    (X₂ := Embedded.FamilyOpenCover.overOpenCoverObject E C k ⊗ A.scheme)
    (Y := T ⊗ A.scheme) (Y' := U ⊗ A.scheme)
    (L₁ := (D.line i).lineBundle.sheaf) (L₂ := (D.line k).lineBundle.sheaf)
    (f₁ := a ▷ A.scheme) (f₂ := b ▷ A.scheme)
    (D.comparison i k a b h).underlying.hom (t ▷ A.scheme) (a' ▷ A.scheme) (b' ▷ A.scheme)
    ((comp_whiskerRight t a A.scheme).symm.trans (congrArg (fun f => f ▷ A.scheme) ha))
    ((comp_whiskerRight t b A.scheme).symm.trans (congrArg (fun f => f ▷ A.scheme) hb))
  exact hp.trans (D.comparison_nativePullback i k a b h t a' b' ha hb h')

/-- All-test comparisons of the original line objects, retaining the
actual module pullback operation on schemes over the fixed base. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.productComparisons : Product.FamilyIntrinsicDescent.ProductFamilyComparisons (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) A.scheme
    (fun i => Embedded.FamilyOpenCover.overOpenCoverMap E C i) where
  obj i := (D.line i).lineBundle.sheaf
  hom {_T} {i k} a b h := (D.comparison i k a b h).underlying.hom
  hom_self {_T} {i} a := rigidified_hom_identity _ (D.comparison_self i a)
  hom_comp {_T} {i k l} a b c hab hbc :=
    rigidified_hom_composition _ _ _ (D.comparison_comp i k l a b c hab hbc)
  pullHom_hom {_T _U} {i k} t a b h a' b' ha hb h' :=
    comparison_overPullback D i k a b h t a' b' ha hb h'

/-- The product cover of the actual abelian total space. -/
abbrev _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.productCover : (E ⊗ A.scheme).left.OpenCover.{0} :=
  Scheme.Cover.copy (C.pullback₁ (fst E A.scheme).left) C.I₀
    (fun i => (Embedded.FamilyOpenCover.overOpenCoverObject E C i ⊗ A.scheme).left)
    (fun i => (Embedded.FamilyOpenCover.overOpenCoverMap E C i ▷ A.scheme).left) (Equiv.refl _)
    (fun i => (Picard.TestFamilyPullback.familySchemeFunctor_map_isPullback A.scheme (Embedded.FamilyOpenCover.overOpenCoverMap E C i)).isoPullback)
    (fun i => (Picard.TestFamilyPullback.familySchemeFunctor_map_isPullback A.scheme
      (Embedded.FamilyOpenCover.overOpenCoverMap E C i)).isoPullback_hom_fst.symm)

/-- The actual native descent datum, including arbitrary scheme tests
which are not themselves entire abelian fibers. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.productDatum : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.productCover (A := A) (E := E) (C := C)).f :=
  Picard.PoincareBundle.UnderlyingDescent.underlyingDatum Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    (fun i => Embedded.FamilyOpenCover.overOpenCoverMap E C i ▷ A.scheme) D.productComparisons.descentData

/-- An actual line object on the whole product, before final global
zero normalization. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.lineObject : Line.Bundles.LineBundle (E ⊗ A.scheme).left :=
  Open.CoverLineObjectDescent.OpenCoverLineObjectDescent.lineBundle (RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.productCover (A := A) (E := E) (C := C))
    D.productDatum (fun i => (D.line i).lineBundle.locallyTrivial)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.lineObject_recovery (i : C.I₀) :
    (D.lineObject.pullback (Embedded.FamilyOpenCover.overOpenCoverMap E C i ▷ A.scheme).left).sheaf ≅
      (D.line i).lineBundle.sheaf :=
  Open.CoverLineObjectDescent.OpenCoverLineObjectDescent.recovery (RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.productCover (A := A) (E := E) (C := C))
    D.productDatum (fun i => (D.line i).lineBundle.locallyTrivial) i

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.lineObject_recovery_class (i : C.I₀) :
    Line.Bundles.LineBundle.pullbackClass (Embedded.FamilyOpenCover.overOpenCoverMap E C i ▷ A.scheme).left
      (Line.Bundles.LineBundle.classOf D.lineObject) = Line.Bundles.LineBundle.classOf (D.line i).lineBundle :=
  Quotient.sound ⟨D.lineObject_recovery i⟩

/-- Normalize the descended line once on the global zero section. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.normalizedLineObject : Line.Bundles.LineBundle (E ⊗ A.scheme).left :=
  ReferenceFamily.Intrinsic.LineNormalization.normalizedNativeLine A E D.lineObject

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.normalizedLineObject_zero :
    (D.normalizedLineObject.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A E).left).sheaf ≅ Line.Bundles.structureModule E.left :=
  Classical.choice (ReferenceFamily.Intrinsic.LineNormalization.normalizedNativeLine_zero A E D.lineObject)

/-- Global normalization preserves each original locally normalized
line object, without requiring auxiliary choices of recovery frames. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.normalizedLineObject_recovery_class (i : C.I₀) :
    Line.Bundles.LineBundle.pullbackClass (Embedded.FamilyOpenCover.overOpenCoverMap E C i ▷ A.scheme).left
      (Line.Bundles.LineBundle.classOf D.normalizedLineObject) = Line.Bundles.LineBundle.classOf (D.line i).lineBundle :=
  ReferenceFamily.Intrinsic.LineNormalization.normalizedNativeLine_recovery A E D.lineObject (Embedded.FamilyOpenCover.overOpenCoverMap E C i)
    (D.line i).lineBundle (D.line i).rigidification (D.lineObject_recovery_class i)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines.DirectedRigidifiedFamilyLines.normalizedLineObject_recovery (i : C.I₀) :
    (D.normalizedLineObject.pullback (Embedded.FamilyOpenCover.overOpenCoverMap E C i ▷ A.scheme).left).sheaf ≅
      (D.line i).lineBundle.sheaf :=
  Classical.choice (Quotient.exact (D.normalizedLineObject_recovery_class i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedLineObjectDescent.DirectedRigidifiedFamilyLines
