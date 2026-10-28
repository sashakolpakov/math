import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramProduct

/-! # Diagram Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DiagramCechProduct

noncomputable section

/-! Native products on the genuine relative resolution of any diagram
of bounded crystalline frames, before geometric specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v z
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{z} C] [HasBinaryProducts C]
  (F : C ⥤ BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p)
  (J := J) (δ := δ) (f := f) (n := n)

abbrev diagram := F.op ⋙ GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor f n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DiagramCechProduct.diagram f n F

def localPairing (a b : ℕ) (V : Cᵒᵖ) (T : Dᵒᵖ) :
    (((P).obj V).X a).obj T →ₗ[B] (((P).obj V).X b).obj T →ₗ[B]
      (((P).obj V).X (a+b)).obj T :=
  RelativeCrystalline.Product.sectionPairing
    (Diagram.productDiagram (F.obj V.unop)) Q
    (Diagram.projection (F.obj V.unop)) a b T

omit [HasBinaryProducts C] in
theorem site_natural (a b : ℕ) (V : Cᵒᵖ) {T T' : Dᵒᵖ} (α : T ⟶ T')
    (x : (((P).obj V).X a).obj T) (y : (((P).obj V).X b).obj T) :
    (((P).obj V).X (a+b)).map α (localPairing f n F a b V T x y) =
      localPairing f n F a b V T'
        ((((P).obj V).X a).map α x) ((((P).obj V).X b).map α y) :=
  RelativeCrystalline.Product.sectionPairing_natural _ Q _ a b α x y

omit [HasBinaryProducts C] in
theorem frame_natural (a b : ℕ) {V V' : Cᵒᵖ} (α : V ⟶ V') (T : Dᵒᵖ)
    (x : (((P).obj V).X a).obj T) (y : (((P).obj V).X b).obj T) :
    (((P).map α).f (a+b)).app T (localPairing f n F a b V T x y) =
      localPairing f n F a b V' T
        ((((P).map α).f a).app T x) ((((P).map α).f b).app T y) :=
  Relative.DiagramProduct.map_pairing _ _ Q _ _
    (Change.diagramMap (F.map α.unop))
    (Change.projection (F.map α.unop)) a b T x y

variable {ι : Type} [Finite ι] (U : ι → C)

def pairing := Cech.PresheafDiagramProduct.pairing B U P (localPairing f n F)
abbrev pairing_natural := Cech.PresheafDiagramProduct.naturality B U P
  (localPairing f n F) (site_natural f n F)
abbrev local_differential (a b : ℕ) (T : Dᵒᵖ) (V : Cᵒᵖ) :=
  RelativeCrystalline.Product.sectionPairing_differential
    (Diagram.productDiagram (F.obj V.unop)) Q
    (Diagram.projection (F.obj V.unop)) a b T
abbrev pairing_differential := Cech.PresheafDiagramProduct.differential B U P
  (localPairing f n F) (frame_natural f n F) (local_differential f n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DiagramCechProduct
