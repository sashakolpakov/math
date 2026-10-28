import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Cech Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

noncomputable section

/-!
# The global invariant sheaf constructed directly from geometric Čech gluing
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)

/-- The canonical direct-image comparison of two equal composites of scheme morphisms. -/
def directImageIso : Scheme.Modules.pushforward p ⋙ Scheme.Modules.pushforward f ≅
    Scheme.Modules.pushforward q ⋙ Scheme.Modules.pushforward f :=
  Scheme.Modules.pushforwardComp p f ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    (Scheme.Modules.pushforwardComp q f).symm

/-- The canonical adjunction comparison of the two iterated geometric pullbacks. -/
def pullbackIso : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback p ≅
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback q :=
  AdjointCechInvariant.pullbackGluing (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (directImageIso f p q h)

variable (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- The invariant object is a globally defined sheaf, formed using an actual equalizer. -/
def invariantSheaf : Y.Modules :=
  AdjointCechInvariant.invariants (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction q) (directImageIso f p q h) σ.hom

/-- The pullback comparison from this invariant sheaf to the original geometric sheaf. -/
def comparison : (Scheme.Modules.pullback f).obj (invariantSheaf f p q h M σ) ⟶ M :=
  AdjointCechInvariant.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (directImageIso f p q h) σ.hom

/-- The comparison respects the actual supplied gluing isomorphism. -/
theorem comparison_compatible :
    (Scheme.Modules.pullback p).map (comparison f p q h M σ) ≫ σ.hom =
      (pullbackIso f p q h).hom.app (invariantSheaf f p q h M σ) ≫
        (Scheme.Modules.pullback q).map (comparison f p q h M σ) :=
  AdjointCechInvariant.comparison_compatible (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (directImageIso f p q h) σ.hom

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (D : KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- The ordinary descent gluing on the actual scheme-theoretic fiber product. -/
def relationGluing :
    (Scheme.Modules.pullback (pullback.fst f f)).obj (D.obj PUnit.unit) ≅
      (Scheme.Modules.pullback (pullback.snd f f)).obj (D.obj PUnit.unit) :=
  D.iso (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (pullback.fst f f) (pullback.snd f f) pullback.condition rfl

/-- A global invariant sheaf for the ordinary geometric descent datum. -/
def ordinaryInvariantSheaf : Y.Modules :=
  invariantSheaf f (pullback.fst f f) (pullback.snd f f) pullback.condition
    (D.obj PUnit.unit) (relationGluing f D)

/-- Its canonical geometric comparison to the original object on the cover. -/
def ordinaryComparison : (Scheme.Modules.pullback f).obj (ordinaryInvariantSheaf f D) ⟶
    D.obj PUnit.unit :=
  comparison f (pullback.fst f f) (pullback.snd f f) pullback.condition
    (D.obj PUnit.unit) (relationGluing f D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant
