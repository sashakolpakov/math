import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Reindex Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexData

noncomputable section

/-! Inverse images identify the original relative Cech coefficients
and their local and global ordered complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)

abbrev preimage : Opens X ⥤ Opens Y := Opens.map f

local instance preimage_limits : PreservesFiniteLimits (preimage f) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.frameHom).toFunctor
  infer_instance

variable (U : Opens X) {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (P : (Opens Y)ᵒᵖ ⥤ A)

def presheafIso :
    Intersections.presheaf U ((preimage f).op ⋙ P) ≅
      (preimage f).op ⋙ Intersections.presheaf ((preimage f).obj U) P :=
  Iso.refl _

def sourceIso :
    (Total.localFunctor U V).obj ((preimage f).op ⋙ P) ≅
    (Total.localFunctor ((preimage f).obj U) ((preimage f).obj ∘ V)).obj P :=
  AugmentedOrdered.CechReindex.iso (preimage f) V
      (Intersections.presheaf ((preimage f).obj U) P)

omit [HasCoproducts A] in
theorem source_naturality {Q : (Opens Y)ᵒᵖ ⥤ A} (a : P ⟶ Q) :
    (Total.localFunctor U V).map (Functor.whiskerLeft (preimage f).op a) ≫
        (sourceIso f U V Q).hom =
      (sourceIso f U V P).hom ≫
        (Total.localFunctor ((preimage f).obj U) ((preimage f).obj ∘ V)).map a := by
  exact AugmentedOrdered.CechReindex.naturality (preimage f) V
    (Intersections.presheaf ((preimage f).obj U) P)
    (Functor.whiskerLeft (Intersections.intersect ((preimage f).obj U)).op a)

omit [LinearOrder ι] in
theorem cover_eq : (preimage f).obj ∘ Intersections.cover U V =
    Intersections.cover ((preimage f).obj U) ((preimage f).obj ∘ V) := by
  funext j
  cases j <;> rfl

def targetIso :
    OrderedCech.Projection.complex (Intersections.cover U V)
      ((preimage f).op ⋙ P) ≅
    OrderedCech.Projection.complex
      (Intersections.cover ((preimage f).obj U) ((preimage f).obj ∘ V)) P :=
  OrderedCech.Reindex.iso (preimage f) (Intersections.cover U V) P ≪≫
    eqToIso (congrArg (fun W => OrderedCech.Projection.complex W P) (cover_eq f U V))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexData
