import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

/-! # Origin -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Origin

noncomputable section

/-!
# Origins of the represented Picard functors for PoincareBundle

The origin is the actual trivial line-bundle class. Geometric pullback
preserves it, and so do the morphisms of represented duals.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

/-- The isomorphism class of the actual structure line bundle. -/
def trivialLineClass (X : Scheme.{u}) : Line.Bundles.LineBundleClass X :=
  Line.Bundles.LineBundleClass.mk (Line.Bundles.LineBundle.trivial X)

@[simp]
theorem pullback_trivialLineClass {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Line.Bundles.LineBundleClass.pullback f (trivialLineClass Y) = trivialLineClass X := by
  apply Quotient.sound
  exact ⟨Line.Bundles.pullbackUnitIso f⟩

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

/-- The trivial relative line class is homogeneous on every test scheme. -/
theorem trivialLineClass_isHomogeneous (T : Over S) :
    Homogeneous.IsHomogeneous A T (trivialLineClass (T ⊗ A).left) := by
  intro U h a
  apply congrArg (fun q => (Functor.toRelativePicard A).app (op U) q)
  change Line.Bundles.LineBundleClass.pullback (Homogeneous.translation A a).left
      (Line.Bundles.LineBundleClass.pullback ((Functor.familySchemeFunctor A).map h) (trivialLineClass _)) =
    Line.Bundles.LineBundleClass.pullback ((Functor.familySchemeFunctor A).map h) (trivialLineClass _)
  erw [pullback_trivialLineClass, pullback_trivialLineClass]

/-- The trivial class in the homogeneous presheaf. -/
def trivialHomogeneousPresheaf (T : Over S) : (Homogeneous.homogeneousPresheaf A).obj (op T) :=
  ⟨trivialLineClass (T ⊗ A).left, trivialLineClass_isHomogeneous A T⟩

/-- The origin section in the actual homogeneous Picard sheaf. -/
def trivialHomogeneousClass (T : Over S) : (Homogeneous.homogeneousSheaf A).obj.obj (op T) :=
  (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T)
    (trivialHomogeneousPresheaf A T)

theorem trivialHomogeneousPresheaf_naturality {T U : Over S} (h : U ⟶ T) :
    (Homogeneous.homogeneousPresheaf A).map h.op (trivialHomogeneousPresheaf A T) =
      trivialHomogeneousPresheaf A U := by
  apply Subtype.ext
  exact pullback_trivialLineClass ((Functor.familySchemeFunctor A).map h)

theorem trivialHomogeneousClass_naturality {T U : Over S} (h : U ⟶ T) :
    (Homogeneous.homogeneousSheaf A).obj.map h.op (trivialHomogeneousClass A T) =
      trivialHomogeneousClass A U := by
  dsimp only [trivialHomogeneousClass]
  erw [← (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).naturality_apply h.op]
  rw [trivialHomogeneousPresheaf_naturality]

variable {A} {B Adual Bdual : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- Pullback preserves the trivial class before sheafification. -/
theorem pullbackHomogeneousPresheaf_trivial (T : Over S) :
    (Homogeneous.pullbackHomogeneousPresheaf f).app (op T) (trivialHomogeneousPresheaf B T) =
      trivialHomogeneousPresheaf A T := by
  apply Subtype.ext
  exact pullback_trivialLineClass (Functor.familyMap f T)

/-- The actual homogeneous Picard pullback preserves the origin. -/
theorem pullbackHomogeneousSheaf_trivial (T : Over S) :
    (Homogeneous.pullbackHomogeneousSheaf f).hom.app (op T) (trivialHomogeneousClass B T) =
      trivialHomogeneousClass A T := by
  have h := congrArg (fun b => b.app (op T) (trivialHomogeneousPresheaf B T))
    (toSheafify_naturality (Scheme.fppfTopology.over S) (Homogeneous.pullbackHomogeneousPresheaf f))
  exact h.symm.trans (congrArg
    (fun q => (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) q)
      (pullbackHomogeneousPresheaf_trivial f T))

/-- The origin on every test scheme in a represented homogeneous Picard functor. -/
def representedOrigin (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Adual) (T : Over S) :
    T ⟶ Adual := DA.homEquiv.symm (trivialHomogeneousClass A T)

/-- The represented origins form a natural section of the represented functor. -/
theorem representedOrigin_naturality
    (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Adual)
    {T U : Over S} (h : U ⟶ T) :
    h ≫ representedOrigin DA T = representedOrigin DA U := by
  apply DA.homEquiv.injective
  rw [DA.homEquiv_comp]
  dsimp only [representedOrigin]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, trivialHomogeneousClass_naturality]

/-- Membership in the fiber of the dual map over the origin is exactly
triviality of the pulled-back homogeneous Picard class. -/
theorem representedDualMap_eq_origin_iff
    (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Adual)
    (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual)
    {T : Over S} (x : T ⟶ Bdual) :
    x ≫ DualMaps.representedDualMap DA DB f = representedOrigin DA T ↔
      (Homogeneous.pullbackHomogeneousSheaf f).hom.app (op T) (DB.homEquiv x) =
        trivialHomogeneousClass A T := by
  rw [← DA.homEquiv.injective.eq_iff, DualMaps.representedDualMap_action]
  dsimp only [representedOrigin]
  rw [Equiv.apply_symm_apply]

/-- The induced dual morphism preserves the represented origin on every test scheme. -/
theorem representedDualMap_origin
    (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Adual)
    (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual) (T : Over S) :
    representedOrigin DB T ≫ DualMaps.representedDualMap DA DB f = representedOrigin DA T := by
  apply DA.homEquiv.injective
  rw [DualMaps.representedDualMap_action]
  dsimp only [representedOrigin]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, pullbackHomogeneousSheaf_trivial]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Origin
