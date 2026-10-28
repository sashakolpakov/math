import OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingSlice
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Presheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafRestriction.PresheafRestrictionQuasiIso

noncomputable section

/-! Exact restriction of presheaf complexes and descent to an incoming slice. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' w z
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {V : Type w} [Category.{z} V] [Abelian V]

def restriction (F : C ⥤ D) : (Dᵒᵖ ⥤ V) ⥤ (Cᵒᵖ ⥤ V) :=
  (Functor.whiskeringLeft _ _ _).obj F.op

instance additive (F : C ⥤ D) : (restriction (V := V) F).Additive := by
  dsimp [restriction]
  infer_instance

instance preservesHomology (F : C ⥤ D) : (restriction (V := V) F).PreservesHomology := by
  let : PreservesFiniteLimits (restriction (V := V) F) := by
    dsimp [restriction]
    infer_instance
  let : PreservesFiniteColimits (restriction (V := V) F) := by
    dsimp [restriction]
    infer_instance
  infer_instance

instance reflectsIsomorphisms (F : C ⥤ D) [F.IsEquivalence] :
    (restriction (V := V) F).ReflectsIsomorphisms := by
  dsimp [restriction]
  infer_instance

variable (F : C ⥤ D) [F.Full] [F.Faithful] (L : IntegralComparison.SiteLifts.IncomingLifts F) (I : C)
  {K M : CochainComplex (Dᵒᵖ ⥤ V) ℕ} (φ : K ⟶ M)

include L in
theorem onSlice [QuasiIso (((restriction (V := V) F).mapHomologicalComplex (.up ℕ)).map φ)] :
    QuasiIso (((restriction (V := V) (Over.forget (F.obj I))).mapHomologicalComplex (.up ℕ)).map φ) := by
  let := IncomingSlice.IncomingSliceEquivalence.essSurj F L I
  let : (Over.post (X := I) F).IsEquivalence := {}
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (restriction (V := V) (Over.post (X := I) F))).mp
  change QuasiIso (((restriction (V := V) (Over.forget I)).mapHomologicalComplex (.up ℕ)).map
    (((restriction (V := V) F).mapHomologicalComplex (.up ℕ)).map φ))
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafRestriction.PresheafRestrictionQuasiIso
