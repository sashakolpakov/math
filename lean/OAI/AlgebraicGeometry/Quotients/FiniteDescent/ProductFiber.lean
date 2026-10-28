import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FamilyCechBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoverConstructionEquality
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianBundle

/-! # Product Fiber -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFiber

noncomputable section

/-! On a trivial integral product fiber, the actual base-changed axes
jointly detect first Cech cohomology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ProductFiberAxisDetection

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes OAI.AlgebraicGeometry.Quotients.FiniteDescent.FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange

variable {K : Type u} [Field K] {X Y S X' Y' : Scheme.{u}}
variable (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ Spec (.of K)) (g' : Y' ⟶ Spec (.of K))
variable (p : X' ⟶ X) (q : Y' ⟶ Y) (t : Spec (.of K) ⟶ S)
variable (hp : IsPullback p f' f t) (hq : IsPullback q g' g t)
variable {ι κ : Type u}
variable (U : ι → X.Opens) (V : κ → Y.Opens)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)

include hi₀ in
theorem left_point_open : ⊤ ≤ ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection f f' p t hp sX hsX ⁻¹ᵁ (p ⁻¹ᵁ U i₀) := by
  change ⊤ ≤ (ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection f f' p t hp sX hsX ≫ p) ⁻¹ᵁ U i₀
  rw [ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection, hp.lift_fst]
  exact fun x _ => hi₀ (show t x ∈ (⊤ : S.Opens) from trivial)

include hj₀ in
theorem right_point_open : ⊤ ≤ ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection g g' q t hq sY hsY ⁻¹ᵁ (q ⁻¹ᵁ V j₀) := by
  change ⊤ ≤ (ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection g g' q t hq sY hsY ≫ q) ⁻¹ᵁ V j₀
  rw [ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection, hq.lift_fst]
  exact fun x _ => hj₀ (show t x ∈ (⊤ : S.Opens) from trivial)

theorem cover_eq : FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.pulledCover f g f' g' p q t hp hq U V =
    CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f' g' (fun a => p ⁻¹ᵁ U a) (fun a => q ⁻¹ᵁ V a) := by
  funext a
  exact ProductBaseOpens.Construction.ProductBaseChangeOpens.rectangle f g f' g' p q t hp hq (U a.1) (V a.2)

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (M : (pullback f g).Modules)
variable [IsIntegral X'] [IsIntegral Y'] [UniversallyClosed f'] [UniversallyClosed g']
variable (hU : ∀ a, IsAffineOpen (p ⁻¹ᵁ U a)) (hV : ∀ a, IsAffineOpen (q ⁻¹ᵁ V a))
variable (hUU : ∀ a b, IsAffineOpen ((p ⁻¹ᵁ U a) ⊓ (p ⁻¹ᵁ U b)))
variable (hVV : ∀ a b, IsAffineOpen ((q ⁻¹ᵁ V a) ⊓ (q ⁻¹ᵁ V b)))
variable (hcU : iSup (fun a => p ⁻¹ᵁ U a) = ⊤) (hcV : iSup (fun a => q ⁻¹ᵁ V a) = ⊤)

include hU hV hUU hVV hcU hcV

theorem jointly
    (e : (Scheme.Modules.pullback (FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.baseMap f g f' g' p q t hp hq)).obj M ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f' g')) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      (FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.fiberLeft f g f' g' p q t hp hq U V sY hsY j₀ hj₀ M)
      (FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.fiberRight f g f' g' p q t hp hq U V sX hsX i₀ hi₀ M) := by
  let M' := (Scheme.Modules.pullback (FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.baseMap f g f' g' p q t hp hq)).obj M
  let sX' := ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection f f' p t hp sX hsX
  let sY' := ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection g g' q t hq sY hsY
  have hi := left_point_open f f' p t hp U sX hsX i₀ hi₀
  have hj := right_point_open g g' q t hq V sY hsY j₀ hj₀
  let E := CechCoverConstructionEquality.Construction.CechCoverEquality.iso (pullback.fst f' g' ≫ f') M'
    (cover_eq f g f' g' p q t hp hq U V)
  apply CechBoundary.Construction.CechBoundaryTransport.jointly_of_iso _ _
    (TrivialProduct.Construction.TrivialProductAxisDetection.left f' g' (fun a => p ⁻¹ᵁ U a) (fun a => q ⁻¹ᵁ V a)
      M' sY' (ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over g g' q t hq sY hsY) j₀ hj)
    (TrivialProduct.Construction.TrivialProductAxisDetection.right f' g' (fun a => p ⁻¹ᵁ U a) (fun a => q ⁻¹ᵁ V a)
      M' sX' (ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over f f' p t hp sX hsX) i₀ hi) E (𝟙 _) (𝟙 _)
  · simpa only [Category.comp_id, FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.fiberLeft, TrivialProduct.Construction.TrivialProductAxisDetection.left,
      ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedLeft, ProductBaseAxes.Construction.ProductBaseChangeAxes.left, CubeProductSlices.Construction.CubeCech.productSliceLeft, E, M', sY'] using
      (CechCoverConstructionEquality.Construction.CechCoverEquality.source (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedLeft g f' g' q t hq sY hsY)
        (pullback.fst f' g' ≫ f') f' (ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over f' g' _ _) M'
        (cover_eq f g f' g' p q t hp hq U V) (fun a => p ⁻¹ᵁ U a) (fun a => ⟨a, j₀⟩)
        (FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.left_refines f g f' g' p q t hp hq U V sY hsY j₀ hj₀)
        (fun a => CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f' g' sY'
          (ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over g g' q t hq sY hsY) (p ⁻¹ᵁ U a) (q ⁻¹ᵁ V j₀) hj)).symm
  · simpa only [Category.comp_id, FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.fiberRight, TrivialProduct.Construction.TrivialProductAxisDetection.right,
      ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedRight, ProductBaseAxes.Construction.ProductBaseChangeAxes.right, CubeProductRightSlice.Construction.CubeCech.productSliceRight, E, M', sX'] using
      (CechCoverConstructionEquality.Construction.CechCoverEquality.source (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedRight f f' g' p t hp sX hsX)
        (pullback.fst f' g' ≫ f') g' (ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over f' g' _ _) M'
        (cover_eq f g f' g' p q t hp hq U V) (fun a => q ⁻¹ᵁ V a) (fun a => ⟨i₀, a⟩)
        (FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.right_refines f g f' g' p q t hp hq U V sX hsX i₀ hi₀)
        (fun a => CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f' g' sX'
          (ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over f f' p t hp sX hsX) (p ⁻¹ᵁ U i₀) (q ⁻¹ᵁ V a) hi)).symm
  · exact TrivialProduct.Construction.TrivialProductAxisDetection.jointly f' g' (fun a => p ⁻¹ᵁ U a)
      (fun a => q ⁻¹ᵁ V a) M' hU hV hUU hVV sX' (ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over f f' p t hp sX hsX)
      sY' (ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over g g' q t hq sY hsY) i₀ hi j₀ hj hcU hcV e

end Construction.ProductFiberAxisDetection

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFiber
